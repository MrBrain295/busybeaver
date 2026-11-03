import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-!
# Kernel-friendly formulation of the event runner

Same semantics as `Sim.lean`, but every function body is kept small: each
`match` alternative is a call to a separate top-level definition.  The kernel
unfolds a definition by instantiating its whole body, so one large function
with many inline alternatives costs time proportional to its total size on
every call.
-/

namespace Sk1.F

variable {R : Type} (o : ROps R)

/-! ### right-moving, item popped -/

def rEnd (c : St R) : Option (St R) :=
  match c.l with
  | .x (n + 1) :: l => some ⟨false, lx n l, o.push (o.push (o.push c.r .P) (.x 1)) .C⟩
  | .D :: l => some ⟨false, l, o.push c.r (.x 1)⟩
  | _ => none

def rC (l : List LS) (r : R) : Option (St R) :=
  match l with
  | .x (n + 1) :: l => some ⟨true, .C0 :: lx n l, r⟩
  | .D :: l => some ⟨true, .x 1 :: .P :: l, r⟩
  | .C0 :: l => some ⟨true, .G0 :: l, r⟩
  | .C2 :: l => some ⟨true, .F0 :: l, r⟩
  | _ => none

def rPD3 (l : List LS) : Option (RI × R) → Option (St R)
  | some (.x (n + 1), r3) => some ⟨true, .D :: .C1 :: l, o.push (o.push r3 (.x n)) .P⟩
  | some (.D, r3) => (unx o r3).map fun r4 => ⟨true, .D :: .C1 :: .C2 :: l, r4⟩
  | some (.C, r3) => (unx o r3).map fun r4 => ⟨true, .D :: .G1 :: l, o.push r4 .P⟩
  | some (.P, r3) => some ⟨true, .D :: .C1 :: l, r3⟩
  | some (.G n, r3) => some ⟨true, lH n l, o.push (o.push r3 .D) .P⟩
  | _ => none

def rP2 (c : St R) : Option (RI × R) → Option (St R)
  | none => some ⟨false, c.l, c.r⟩
  | some (.x n, r2) => some ⟨true, lx n c.l, o.push r2 .P⟩
  | some (.D, r2) => rPD3 o c.l (o.pop r2)
  | some (.C, r2) => (unx o r2).map fun r3 => ⟨false, c.l, o.push (o.push (o.push r3 .P) .D) .P⟩
  | some (.P, r2) => some ⟨true, lx 1 c.l, r2⟩
  | _ => none

def rItem (c : St R) : Option (RI × R) → Option (St R)
  | none => rEnd o c
  | some (.x n, r) => some ⟨true, lx n c.l, r⟩
  | some (.D, r) => some ⟨true, .D :: c.l, r⟩
  | some (.C, r) => rC c.l r
  | some (.P, r1) => rP2 o c (o.pop r1)
  | some (.G n, r) => some ⟨true, lG n c.l, r⟩

/-! ### left-moving -/

def lEmpty (r : R) : Option (RI × R) → Option (St R)
  | some (.C, r) => (unx o r).map fun r => ⟨true, [.D, .C1], o.push r .P⟩
  | _ => none

def lF3 (r : R) : List LS → Option (St R)
  | .x (n + 1) :: l => some ⟨true, .D :: .C1 :: .P :: lx n l, r⟩
  | _ => none

def lSym (r : R) (l : List LS) : LS → Option (St R)
  | .x n => some ⟨false, l, o.push r (.x n)⟩
  | .D => some ⟨false, l, o.push r .D⟩
  | .P => some ⟨false, l, o.push r .P⟩
  | .C0 => some ⟨true, .x 1 :: .C1 :: l, r⟩
  | .C1 => some ⟨true, .C2 :: l, r⟩
  | .C2 => some ⟨true, .x 1 :: .C3 :: l, r⟩
  | .C3 => some ⟨false, l, o.push r .C⟩
  | .F0 => some ⟨true, .x 1 :: .F1 :: l, r⟩
  | .F1 => some ⟨true, .F2 :: l, r⟩
  | .F2 => some ⟨true, .x 1 :: .F3 :: l, r⟩
  | .F3 => lF3 r l
  | .G0 => some ⟨true, .x 1 :: .G1 :: l, r⟩
  | .G1 => some ⟨true, .G2 :: l, r⟩
  | .G2 => some ⟨true, .x 1 :: .D :: .P :: l, r⟩
  | .Gs n => some ⟨false, l, o.push r (.G n)⟩
  | _ => none

def lStep (r : R) : List LS → Option (St R)
  | [] => lEmpty o r (o.pop r)
  | s :: l => lSym o r l s

def simple (c : St R) : Option (St R) :=
  match c.right with
  | true => rItem o c (o.pop c.r)
  | false => lStep o c.r c.l

def ev (e : Nat) (c : St R) : Option (St R) :=
  match e with
  | 0 => F.simple o c
  | 1 => tickSt o c
  | _ => uniSt o c

def step64 (ih : Nat → St R → Option (St R)) (g : Nat) : Option (St R) → Option (St R)
  | some c' => ih (g / 4) c'
  | none => none

def run64 (k : Nat) : Nat → St R → Option (St R) :=
  Nat.rec (motive := fun _ => Nat → St R → Option (St R))
    (fun _ c => some c)
    (fun _ ih g c => step64 ih g (F.ev o (g % 4) c))
    k

def stepG (ih : List Nat → St R → Option (St R)) (gs : List Nat) : Option (St R) → Option (St R)
  | some c' => ih gs c'
  | none => none

def runG (fuel : Nat) : List Nat → St R → Option (St R) :=
  Nat.rec (motive := fun _ => List Nat → St R → Option (St R))
    (fun _ c => some c)
    (fun _ ih gs c =>
      match gs with
      | [] => some c
      | g :: gs => stepG ih gs (F.run64 o 64 g c))
    fuel

/-- Run event groups `(number of events, packed event codes)`.  Unlike `runG`,
the last group need not contain 64 events. -/
def runPacked (o : ROps R) (gs : List (Nat × Nat)) (c : St R) : Option (St R) :=
  match gs with
  | [] => some c
  | (n, code) :: gs =>
    match F.run64 o n code c with
    | some c' => F.runPacked o gs c'
    | none => none

end Sk1.F
