import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-!
# Untrusted trace generator (not part of any proof)

Runs the eager simulator from the initial configuration, choosing events the
way the accelerated simulator does (universal cycle if possible, else a tick if
possible, else a simple step), and emits benchmark/certificate chunks.
-/

namespace Sk1.Gen

def Kc : List RI :=
  [.x 7639, .D, .x 10347, .C, .x 7635, .D, .x 10355, .C, .x 7619, .D, .x 10387, .C,
   .x 7555, .D, .x 10515, .C, .x 7299, .D, .x 11027, .C, .x 6275, .D, .x 13075, .C,
   .x 2179, .D, .D, .x 7088, .C, .x 1, .C, .x 3849, .P]

def isCyc (c : St (List RI)) : Bool :=
  c.right && (match c.l with | .C0 :: _ => true | _ => false) && c.r == Kc

def initial : St (List RI) := ⟨true, [.C1], [.P]⟩

/-- Choose and execute the next event eagerly. -/
def nextE (c : St (List RI)) : Option (Nat × St (List RI)) :=
  match uniSt eagerOps c with
  | some c' => some (2, c')
  | none =>
    match tickSt eagerOps c with
    | some c' => some (1, c')
    | none => (simple eagerOps c).map fun c' => (0, c')

def lsStr : LS → String
  | .x n => s!".x {n}" | .D => ".D" | .P => ".P" | .C0 => ".C0" | .C1 => ".C1"
  | .C2 => ".C2" | .C3 => ".C3" | .F0 => ".F0" | .F1 => ".F1" | .F2 => ".F2" | .F3 => ".F3"
  | .G0 => ".G0" | .G1 => ".G1" | .G2 => ".G2" | .Fs n => s!".Fs {n}" | .Gs n => s!".Gs {n}"
  | .Hs n => s!".Hs {n}" | .tl => ".tl"

def riStr : RI → String
  | .x n => s!".x {n}" | .D => ".D" | .C => ".C" | .P => ".P" | .G n => s!".G {n}"

def listStr {α} (f : α → String) (l : List α) : String :=
  "[" ++ ", ".intercalate (l.map f) ++ "]"

def boolStr (b : Bool) : String := if b then "true" else "false"

end Sk1.Gen

open Sk1 Sk1.Gen

/-- `gen <start> <count> <name> <out.lean>` : emit a chunk of `count` events
(multiple of 64) starting after `start` events. -/
def main (args : List String) : IO Unit := do
  match args with
  | [startS, countS, name, out] =>
    let start := startS.toNat!
    let count := countS.toNat!
    let mut c := initial
    for _ in [0:start] do
      match nextE c with
      | some (_, c') => c := c'
      | none => throw (IO.userError "stuck before start")
    let c0 := c
    let mut evs : Array Nat := #[]
    let mut minL := c.l.length
    let mut nUni := 0
    let mut nTick := 0
    for _ in [0:count] do
      match nextE c with
      | some (e, c') =>
        evs := evs.push e
        if e == 2 then nUni := nUni + 1
        if e == 1 then nTick := nTick + 1
        c := c'
        minL := min minL c.l.length
      | none => throw (IO.userError "stuck in chunk")
    let c1 := c
    -- keep only the touched top of the left tape (plus a margin)
    let keep0 := c0.l.length - (minL - min minL 2)
    let keep1 := c1.l.length - (minL - min minL 2)
    let l0 := (c0.l.take keep0) ++ (if keep0 < c0.l.length then [LS.tl] else [])
    let l1 := (c1.l.take keep1) ++ (if keep1 < c1.l.length then [LS.tl] else [])
    -- pack events
    let mut groups : Array Nat := #[]
    let mut i := 0
    while i < evs.size do
      let mut g := 0
      let mut j := 0
      while j < 64 do
        g := g + (evs.getD (i + j) 0) * 4 ^ j
        j := j + 1
      groups := groups.push g
      i := i + 64
    let body := s!"import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-! Generated chunk: events {start}..{start + count} ({nTick} ticks, {nUni} universal cycles). -/

namespace Sk1.{name}

def d0 : Bool := {boolStr c0.right}
def d1 : Bool := {boolStr c1.right}
def l0 : List LS := {listStr lsStr l0}
def r0 : List RI := {listStr riStr c0.r}
def evs : List Nat := {listStr toString groups.toList}
def l1 : List LS := {listStr lsStr l1}
def r1 : List RI := {listStr riStr c1.r}

end Sk1.{name}
"
    IO.FS.writeFile out body
    IO.println s!"wrote {out}: left {c0.l.length}->{c1.l.length} kept {keep0}/{keep1}, right {c0.r.length}->{c1.r.length}, ticks {nTick}, unis {nUni}, groups {groups.size}, dir {c0.right}->{c1.right}"
  | _ => IO.println "usage: gen <start> <count> <name> <out.lean>"
