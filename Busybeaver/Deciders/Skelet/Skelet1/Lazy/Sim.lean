import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Defs

/-!
# Event-driven symbolic simulator, generic in the right-tape representation

The left tape is an ordinary list of left symbols (head-nearest first).  The
right tape is abstract: it is accessed only through `pop`, `push`, `tick` and
(for the rare universal-cycle shortcut) conversion from/to an eager list.  The
simulator is instantiated twice: with eager lists (`List RI`, used by the
untrusted generator) and with the lazy tape `RT` (used in kernel checks).
-/

namespace Sk1

/-- Left tape symbols (head-nearest first).  `tl` marks an abstract left tail
that no rule may inspect. -/
inductive LS
  | x (n : Nat) | D | P | C0 | C1 | C2 | C3 | F0 | F1 | F2 | F3 | G0 | G1 | G2
  | Fs (n : Nat) | Gs (n : Nat) | Hs (n : Nat) | tl
  deriving DecidableEq, Repr

/-! The merging pushes below inspect the top of the left tape.  If that top is
the abstract tail marker `tl`, the result is not determined by the visible part
of the tape, so the push *destroys* the marker (it returns `[]`).  No rule ever
creates `tl`, so a chunk whose final left tape still ends in `tl` never looked
at the abstract tail (see `Frame.lean`).  On `tl`-free tapes these are the
ordinary run-merging pushes. -/

def lx (n : Nat) (l : List LS) : List LS :=
  if n = 0 then l else
  match l with | .x m :: l => .x (n + m) :: l | .tl :: _ => [] | l => .x n :: l

def lF (n : Nat) (l : List LS) : List LS :=
  if n = 0 then l else
  match l with | .Fs m :: l => .Fs (n + m) :: l | .tl :: _ => [] | l => .Fs n :: l

def lG (n : Nat) (l : List LS) : List LS :=
  if n = 0 then l else
  match l with | .Gs m :: l => .Gs (n + m) :: l | .tl :: _ => [] | l => .Gs n :: l

def lH (n : Nat) (l : List LS) : List LS :=
  if n = 0 then l else
  match l with | .Hs m :: l => .Hs (n + m) :: l | .tl :: _ => [] | l => .Hs n :: l

/-- Operations on a right-tape representation. -/
structure ROps (R : Type) where
  pop : R → Option (RI × R)
  push : R → RI → R
  tick : R → Option R
  /-- A sweep with multiplier `m` (`m` ticks at once). -/
  tickN : Nat → R → Option R
  toList : R → Option (List RI)
  ofList : List RI → R

/-- Push one item on an eager tape (runs and `G` blocks merge). -/
def ePush (t : List RI) (i : RI) : List RI :=
  match i with | .x n => pushX n t | .G n => pushG n t | i => i :: t

/-- Eager list operations.  `ofList` re-normalizes (merges adjacent runs and
`G` blocks), which does not change the machine tape that a list stands for. -/
def eagerOps : ROps (List RI) where
  pop := fun t => match t with | [] => none | i :: t => some (i, t)
  push := ePush
  tick := sweep 0 1
  tickN := sweep 0
  toList := some
  ofList := fun t => t.foldr (fun i acc => ePush acc i) []

/-- Build a lazy tape from an eager list (no pending ticks). -/
def RT.ofList (t : List RI) : RT := t.foldr (fun i acc => acc.push i) ⟨⟨[], 0⟩, [], false⟩

/-- Lazy operations. -/
def lazyOps : ROps RT where
  pop := RT.pop
  push := RT.push
  tick := RT.tick
  tickN := RT.tickN
  toList := RT.den
  ofList := RT.ofList

structure St (R : Type) where
  right : Bool
  l : List LS
  r : R
  deriving DecidableEq, Repr

/-- Initial symbolic configuration with the ordinary eager right tape. -/
def init : St (List RI) := ⟨true, [.C1], [.P]⟩

/-- The same initial configuration in the deferred-tick representation. -/
def lazyInit : St RT := ⟨true, [.C1], RT.ofList [.P]⟩

/-- Right-tape shape repeated by the final universal cycle. -/
def Kc : List RI :=
  [.x 7639, .D, .x 10347, .C, .x 7635, .D, .x 10355, .C, .x 7619, .D, .x 10387, .C,
   .x 7555, .D, .x 10515, .C, .x 7299, .D, .x 11027, .C, .x 6275, .D, .x 13075, .C,
   .x 2179, .D, .D, .x 7088, .C, .x 1, .C, .x 3849, .P]

section
variable {R : Type} (o : ROps R)

/-- Peel one `x` off the right tape (a `G` block is expanded first). -/
def unx (t : R) : Option R :=
  match o.pop t with
  | some (.x (n + 1), t) => some (o.push t (.x n))
  | some (.G (n + 1), t) =>
      some ([.x 299, .D, .x 30826, .D, .x 72142, .D, .x 3076, .D, .x 1538, .D].foldr
        (fun i acc => o.push acc i) (o.push t (.G n)))
  | _ => none

/-- One simple symbolic macro step. -/
def simple (c : St R) : Option (St R) :=
  let l := c.l
  let r := c.r
  if c.right then
    match o.pop r with
    | none =>
      match l with
      | .x (n + 1) :: l => some ⟨false, lx n l, o.push (o.push (o.push r .P) (.x 1)) .C⟩
      | .D :: l => some ⟨false, l, o.push r (.x 1)⟩
      | _ => none
    | some (.x n, r) => some ⟨true, lx n l, r⟩
    | some (.D, r) => some ⟨true, .D :: l, r⟩
    | some (.C, r) =>
      match l with
      | .x (n + 1) :: l => some ⟨true, .C0 :: lx n l, r⟩
      | .D :: l => some ⟨true, .x 1 :: .P :: l, r⟩
      | .C0 :: l => some ⟨true, .G0 :: l, r⟩
      | .C2 :: l => some ⟨true, .F0 :: l, r⟩
      | _ => none
    | some (.P, r1) =>
      match o.pop r1 with
      | none => some ⟨false, l, c.r⟩
      | some (.x n, r2) => some ⟨true, lx n l, o.push r2 .P⟩
      | some (.D, r2) =>
        match o.pop r2 with
        | some (.x (n + 1), r3) => some ⟨true, .D :: .C1 :: l, o.push (o.push r3 (.x n)) .P⟩
        | some (.D, r3) => (unx o r3).map fun r4 => ⟨true, .D :: .C1 :: .C2 :: l, r4⟩
        | some (.C, r3) => (unx o r3).map fun r4 => ⟨true, .D :: .G1 :: l, o.push r4 .P⟩
        | some (.P, r3) => some ⟨true, .D :: .C1 :: l, r3⟩
        | some (.G n, r3) => some ⟨true, lH n l, o.push (o.push r3 .D) .P⟩
        | _ => none
      | some (.C, r2) => (unx o r2).map fun r3 => ⟨false, l, o.push (o.push (o.push r3 .P) .D) .P⟩
      | some (.P, r2) => some ⟨true, lx 1 l, r2⟩
      | _ => none
    | some (.G n, r) => some ⟨true, lG n l, r⟩
  else
    match l with
    | [] =>
      match o.pop r with
      | some (.C, r) => (unx o r).map fun r => ⟨true, [.D, .C1], o.push r .P⟩
      | _ => none
    | .x n :: l => some ⟨false, l, o.push r (.x n)⟩
    | .D :: l => some ⟨false, l, o.push r .D⟩
    | .P :: l => some ⟨false, l, o.push r .P⟩
    | .C0 :: l => some ⟨true, .x 1 :: .C1 :: l, r⟩
    | .C1 :: l => some ⟨true, .C2 :: l, r⟩
    | .C2 :: l => some ⟨true, .x 1 :: .C3 :: l, r⟩
    | .C3 :: l => some ⟨false, l, o.push r .C⟩
    | .F0 :: l => some ⟨true, .x 1 :: .F1 :: l, r⟩
    | .F1 :: l => some ⟨true, .F2 :: l, r⟩
    | .F2 :: l => some ⟨true, .x 1 :: .F3 :: l, r⟩
    | .F3 :: .x (n + 1) :: l => some ⟨true, .D :: .C1 :: .P :: lx n l, r⟩
    | .G0 :: l => some ⟨true, .x 1 :: .G1 :: l, r⟩
    | .G1 :: l => some ⟨true, .G2 :: l, r⟩
    | .G2 :: l => some ⟨true, .x 1 :: .D :: .P :: l, r⟩
    | .Gs n :: l => some ⟨false, l, o.push r (.G n)⟩
    | _ => none

/-- A tick (only from a right-moving configuration). -/
def tickSt (c : St R) : Option (St R) :=
  if c.right then (o.tick c.r).map fun r => ⟨false, c.l, r⟩ else none

/-! ### Universal cycle shortcut (eager computation, rare) -/

def uniP : Nat := 53946
def uniT : Nat := 4 * uniP - 5

def Jc : List LS :=
  [.D, .C2, .x 95, .C0,
   .x 7713, .D, .D, .x 1866, .C1,
   .x 13231, .D, .x 6197, .C3,
   .x 11066, .D, .x 7279, .C0,
   .x 10524, .D, .x 7550, .C2,
   .x 10389, .D, .x 7618, .C1,
   .x 10355, .D, .x 7635, .C3,
   .x 10347, .D, .x 7639, .C3,
   .x 10345, .D, .x 7640, .C1]

/-- Largest number of ticks that a right tape supports in one batched sweep. -/
def maxSweep : Nat → List RI → Option Nat
  | _, [.P] => none
  | _, .P :: _ => some 0
  | _, [] => some 0
  | a, .x b :: t => maxSweep (a + b) t
  | _, .D :: t => maxSweep 0 t
  | a, .C :: t =>
      match maxSweep 0 t with
      | some n => some (min a (n / 4))
      | none => some a
  | _, .G _ :: t => maxSweep 0 t

def uniCount (a : Nat) (r : List RI) : Nat :=
  let lim := (a - 1) / uniP
  if lim = 0 then 0 else
  match maxSweep 0 r with
  | some s => min lim (s / uniT)
  | none => lim

def stripP : List LS → List LS → Option (List LS)
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xt, y :: yt => if x = y then stripP xt yt else none

def uniSt (c : St R) : Option (St R) :=
  if c.right then
    match c.l with
    | .D :: .C1 :: .x a :: l =>
      match stripP Jc l with
      | some l =>
        match o.toList c.r with
        | some r =>
          match uniCount a r with
          | 0 => none
          | k + 1 =>
            match sweep 0 ((k + 1) * uniT) r with
            | some r' => some ⟨true, .D :: .C1 :: .x (a - (k + 1) * uniP) :: Jc ++ lF (k + 1) l,
                o.ofList (pushG (k + 1) r')⟩
            | none => none
        | none => none
      | none => none
    | _ => none
  else none

/-- `k ≥ 1` universal cycles at once, with `k` supplied by the certificate.  The
guard `k * uniP < a` and the batched sweep are exactly the conditions under
which `k` cycles are valid; `k` need not be the largest possible count. -/
def uniKSt (k : Nat) (c : St R) : Option (St R) :=
  if c.right then
    match c.l with
    | .D :: .C1 :: .x a :: l =>
      match stripP Jc l with
      | some l =>
        if 0 < k ∧ k * uniP < a then
          match o.tickN (k * uniT) c.r with
          | some r' => some ⟨true, .D :: .C1 :: .x (a - k * uniP) :: Jc ++ lF k l, o.push r' (.G k)⟩
          | none => none
        else none
      | none => none
    | _ => none
  else none

/-- Execute one event. -/
def ev (e : Nat) (c : St R) : Option (St R) :=
  match e with
  | 0 => simple o c
  | 1 => tickSt o c
  | _ => uniSt o c

/-- Run one group of `k ≤ 64` events packed 2 bits each. -/
def run64 (k : Nat) : Nat → St R → Option (St R) :=
  Nat.rec (motive := fun _ => Nat → St R → Option (St R))
    (fun _ c => some c)
    (fun _ ih g c =>
      match ev o (g % 4) c with
      | some c' => ih (g / 4) c'
      | none => none)
    k

/-- Run a list of 64-event groups. -/
def runG (fuel : Nat) : List Nat → St R → Option (St R) :=
  Nat.rec (motive := fun _ => List Nat → St R → Option (St R))
    (fun _ c => some c)
    (fun _ ih gs c =>
      match gs with
      | [] => some c
      | g :: gs =>
        match run64 o 64 g c with
        | some c' => ih gs c'
        | none => none)
    fuel

end

/-- Compare the denotation of a lazy state with an eager configuration. -/
def St.matches (c : St RT) (right : Bool) (l : List LS) (r : List RI) : Bool :=
  c.right == right && c.l == l && c.r.den == some r

end Sk1
