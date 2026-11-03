import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Certified

/-!
# Untrusted certificate writer (not part of any proof)

Pass 2 of the certificate generator.  Replays the event stream produced by the
eager simulator (`explore/gen/certgen2`) with the *lazy* simulator and writes the
chunk files: lazy configurations at segment boundaries (left tapes truncated as
planned) and the grouped event codes.  Everything it writes is re-checked by the
kernel, so nothing here needs to be trusted.

usage: `lazygen <plan dir> <out dir>`
-/

namespace Sk1.LazyGen

def lsStr : LS → String
  | .x n => s!".x {n}" | .D => ".D" | .P => ".P" | .C0 => ".C0" | .C1 => ".C1"
  | .C2 => ".C2" | .C3 => ".C3" | .F0 => ".F0" | .F1 => ".F1" | .F2 => ".F2" | .F3 => ".F3"
  | .G0 => ".G0" | .G1 => ".G1" | .G2 => ".G2" | .Fs n => s!".Fs {n}" | .Gs n => s!".Gs {n}"
  | .Hs n => s!".Hs {n}" | .tl => ".tl"

def sepStr : Sep → String
  | .D => ".D" | .G n => s!".G {n}" | .P => ".P"

def listStr {α} (f : α → String) (l : List α) : String :=
  "[" ++ ", ".intercalate (l.map f) ++ "]"

def boolStr (b : Bool) : String := if b then "true" else "false"

def segStr (g : Seg) : String :=
  "⟨" ++ listStr (fun p => s!"({p.1}, {sepStr p.2})") g.segs ++ s!", {g.trail}⟩"

def blkStr (b : LBlk) : String := "⟨" ++ segStr b.body ++ s!", {b.s}, {b.r}⟩"

def rtStr (t : RT) : String :=
  "⟨" ++ segStr t.top ++ ", " ++ listStr blkStr t.below ++ ", " ++ boolStr t.termP ++ "⟩"

/-- Left tape truncated to `kept` symbols. -/
def leftStr (l : List LS) (kept : Nat) (trunc : Bool) : String :=
  listStr lsStr (if trunc then l.take kept ++ [LS.tl] else l)

def stStr (c : St RT) (kept : Nat) (trunc : Bool) : String :=
  "⟨" ++ boolStr c.right ++ ", " ++ leftStr c.l kept trunc ++ ", " ++ rtStr c.r ++ "⟩"

end Sk1.LazyGen

open Sk1 Sk1.LazyGen

def main (args : List String) : IO Unit := do
  match args with
  | [dir, out] =>
    let plan := (← IO.FS.readFile (dir ++ "/plan.txt")).splitOn "\n" |>.filter (· ≠ "")
    let hdr := (plan.head!.splitOn " ").map String.toNat!
    let E := hdr[1]!
    let fileLines := plan.tail!
    let evs ← IO.FS.readBinFile (dir ++ "/events.bin")
    let uniks := ((← IO.FS.readFile (dir ++ "/uniks.txt")).splitOn "\n").filter (· ≠ "") |>.map String.toNat!
    IO.FS.createDirAll out
    let mut c : St RT := ⟨true, [.C1], RT.ofList [.P]⟩
    let mut pos := 0
    let mut uk := uniks
    let mut prevStr : String := ""
    let mut fi := 0
    for fl in fileLines do
      let nums := (fl.splitOn " ").map String.toNat!
      let K := nums[0]!
      let trunc := nums[1]! == 1
      let kepts := nums.drop 2
      let name := "C" ++ String.mk (List.replicate (4 - (toString fi).length) '0') ++ toString fi
      let mut body := s!"import Busybeaver.Deciders.Skelet.Skelet1.K.K4\nimport Busybeaver.Deciders.Skelet.Skelet1.Cert.Steps\n\nset_option maxRecDepth 200000\n\nnamespace Sk1.Cert.{name}\n\n"
      if fi == 0 then
        body := body ++ s!"def c0 : St RT := {stStr c K trunc}\n\n"
      else
        body := body ++ s!"def p : St RT := {prevStr}\n\n"
        body := body ++ s!"def c0 : St RT := ⟨p.right, {leftStr c.l K trunc}, p.r⟩\n\n"
        body := body ++ "theorem g : K4.glueL p.l c0.l = true := by decide +kernel\n\n"
      let mut j := 0
      for kept in kepts do
        -- run one segment
        let mut groups : Array String := #[]
        let mut rawGroups : Array String := #[]
        let mut rawCode := 0
        let mut rawK := 0
        let mut n := 0
        let mut codes := 0
        let mut k := 0
        let mut ks : Array Nat := #[]
        let mut cnt := 0
        while cnt < E && pos < evs.size do
          let e := evs.get! pos
          let right := c.right
          let mut r : Option (St RT) := none
          if e == 0 then
            r := simple checkedOps c
          else if e == 1 then
            r := tickSt checkedOps c
          else
            match uk with
            | kk :: rest =>
              uk := rest
              ks := ks.push kk
              r := uniKSt checkedOps kk c
            | [] => throw (IO.userError "out of cycle counts")
          match r with
          | some c' => c := c'
          | none => throw (IO.userError s!"lazy simulator stuck at event {pos}")
          if right then
            codes := codes + e.toNat * 4 ^ k
            k := k + 1
          rawCode := rawCode + e.toNat * 4 ^ rawK
          rawK := rawK + 1
          n := n + 1
          cnt := cnt + 1
          pos := pos + 1
          if rawK == 32 then
            rawGroups := rawGroups.push s!"(32, {rawCode})"
            rawCode := 0; rawK := 0
          if k == 32 then
            groups := groups.push s!"({n}, {codes}, {listStr toString ks.toList})"
            n := 0; codes := 0; k := 0; ks := #[]
        if rawK > 0 then
          rawGroups := rawGroups.push s!"({rawK}, {rawCode})"
        if n > 0 then
          groups := groups.push s!"({n}, {codes}, {listStr toString ks.toList})"
        let cs := stStr c kept trunc
        body := body ++ s!"def gs{j} : List (Nat × Nat × List Nat) := {listStr id groups.toList}\n\n"
        body := body ++ s!"def es{j} : List (Nat × Nat) := {listStr id rawGroups.toList}\n\n"
        body := body ++ s!"def c{j+1} : St RT := {cs}\n\n"
        body := body ++ s!"theorem s{j} : K4.checkS gs{j} c{j} c{j+1} = true := by decide +kernel\n\n"
        body := body ++ s!"theorem run{j} : F.runPacked checkedOps es{j} c{j} = some c{j+1} := by decide +kernel\n\n"
        body := body ++ s!"theorem path{j} : Steps checkedOps c{j} c{j+1} := runPacked_steps checkedOps run{j}\n\n"
        prevStr := cs
        j := j + 1
      body := body ++ s!"end Sk1.Cert.{name}\n"
      IO.FS.writeFile (out ++ s!"/{name}.lean") body
      fi := fi + 1
    IO.println s!"wrote {fi} files, {pos} events, final right={c.right} den={(c.r.den.map List.length)}"
  | _ => IO.println "usage: lazygen <plan dir> <out dir>"
