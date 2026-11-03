import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Fast

/-!
# Fourth-generation kernel runner

Measured cost model of the kernel evaluator: time is about 6.4µs per unfolding of
a definition or recursor (`set_option diagnostics true` reports these counts).
So the representation minimizes unfoldings per symbolic event:

* every case split is a direct recursor application (`T.rec`), saving the
  extra unfolding of `T.casesOn`;
* the left tape is the list type `LL` whose constructors carry the symbol;
* the head level of the lazy right tape is an item list `RL`
  (`x a` with `a ≠ 0`, `D`, `G n`, `P`; every `x` is followed by a separator)
  plus its trailing run `tr`; popping or pushing an item is one recursor step;
* the number `pc` of `P` items in the head level is cached (ticks are `O(1)`);
* deferred levels form the flat list type `BL`;
* the direction is the constructor of the state, and only right-moving states
  read an event code.
-/

namespace Sk1.K4

open Sk1

inductive LL
  | nil
  | x (n : Nat) (t : LL) | D (t : LL) | P (t : LL)
  | C0 (t : LL) | C1 (t : LL) | C2 (t : LL) | C3 (t : LL)
  | F0 (t : LL) | F1 (t : LL) | F2 (t : LL) | F3 (t : LL)
  | G0 (t : LL) | G1 (t : LL) | G2 (t : LL)
  | Fs (n : Nat) (t : LL) | Gs (n : Nat) (t : LL) | Hs (n : Nat) (t : LL) | tl (t : LL)

/-- Items of a level, excluding its trailing run. -/
inductive RL
  | nil
  | x (a : Nat) (t : RL)
  | D (t : RL)
  | G (n : Nat) (t : RL)
  | P (t : RL)

/-- Deferred levels: items, trailing run, number of `P`s, pending summary. -/
inductive BL
  | nil
  | cons (body : RL) (tr pc s r : Nat) (rest : BL)

inductive KS
  | L (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool)
  | R (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool)
  | stuck

/-! ### Conversions -/

def LL.ofList : List LS → LL
  | [] => .nil
  | .x n :: t => .x n (ofList t) | .D :: t => .D (ofList t) | .P :: t => .P (ofList t)
  | .C0 :: t => .C0 (ofList t) | .C1 :: t => .C1 (ofList t) | .C2 :: t => .C2 (ofList t)
  | .C3 :: t => .C3 (ofList t) | .F0 :: t => .F0 (ofList t) | .F1 :: t => .F1 (ofList t)
  | .F2 :: t => .F2 (ofList t) | .F3 :: t => .F3 (ofList t) | .G0 :: t => .G0 (ofList t)
  | .G1 :: t => .G1 (ofList t) | .G2 :: t => .G2 (ofList t) | .Fs n :: t => .Fs n (ofList t)
  | .Gs n :: t => .Gs n (ofList t) | .Hs n :: t => .Hs n (ofList t) | .tl :: t => .tl (ofList t)

def LL.toList : LL → List LS
  | .nil => []
  | .x n t => .x n :: toList t | .D t => .D :: toList t | .P t => .P :: toList t
  | .C0 t => .C0 :: toList t | .C1 t => .C1 :: toList t | .C2 t => .C2 :: toList t
  | .C3 t => .C3 :: toList t | .F0 t => .F0 :: toList t | .F1 t => .F1 :: toList t
  | .F2 t => .F2 :: toList t | .F3 t => .F3 :: toList t | .G0 t => .G0 :: toList t
  | .G1 t => .G1 :: toList t | .G2 t => .G2 :: toList t | .Fs n t => .Fs n :: toList t
  | .Gs n t => .Gs n :: toList t | .Hs n t => .Hs n :: toList t | .tl t => .tl :: toList t

def sepRL (sp : Sep) (t : RL) : RL :=
  match sp with
  | .D => .D t
  | .G n => .G n t
  | .P => .P t

def RL.ofSegs : List (Nat × Sep) → RL
  | [] => .nil
  | (a, sp) :: t => if a = 0 then sepRL sp (ofSegs t) else .x a (sepRL sp (ofSegs t))

/-- Segments of an item list; `acc` is a run waiting for its separator. -/
def RL.toSegsAux : Nat → RL → List (Nat × Sep)
  | _, .nil => []
  | a, .x b t => toSegsAux (a + b) t
  | a, .D t => (a, .D) :: toSegsAux 0 t
  | a, .G n t => (a, .G n) :: toSegsAux 0 t
  | a, .P t => (a, .P) :: toSegsAux 0 t

def RL.toSegs (t : RL) : List (Nat × Sep) := toSegsAux 0 t

def RL.countP : RL → Nat
  | .nil => 0
  | .x _ t => countP t
  | .D t => countP t
  | .G _ t => countP t
  | .P t => countP t + 1

def BL.ofList : List LBlk → BL
  | [] => .nil
  | b :: bs => .cons (RL.ofSegs b.body.segs) b.body.trail (RL.countP (RL.ofSegs b.body.segs)) b.s b.r
      (ofList bs)

def BL.toList : BL → List LBlk
  | .nil => []
  | .cons body tr _ s r rest => ⟨⟨body.toSegs, tr⟩, s, r⟩ :: toList rest

def KS.ofSt (c : St RT) : KS :=
  let top := RL.ofSegs c.r.top.segs
  if c.right then .R (LL.ofList c.l) top c.r.top.trail (RL.countP top) (BL.ofList c.r.below) c.r.termP
  else .L (LL.ofList c.l) top c.r.top.trail (RL.countP top) (BL.ofList c.r.below) c.r.termP

def KS.toSt : KS → Option (St RT)
  | .L l top tr _ bl tp => some ⟨false, l.toList, ⟨⟨top.toSegs, tr⟩, bl.toList, tp⟩⟩
  | .R l top tr _ bl tp => some ⟨true, l.toList, ⟨⟨top.toSegs, tr⟩, bl.toList, tp⟩⟩
  | .stuck => none

noncomputable section

/-! ### Eliminators -/

def LL.elimX {α : Sort _} (l : LL) (kx : Nat → LL → α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun n t _ => kx n t)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ => ko) l

/-- Merge eliminators: `kx` on a run of the merged kind, `kt` on the abstract
tail marker, `ko` otherwise. -/
def LL.mergeX {α : Sort _} (l : LL) (kx : Nat → LL → α) (kt : α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun n t _ => kx n t)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ => kt) l

def LL.mergeGs {α : Sort _} (l : LL) (kg : Nat → LL → α) (kt : α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun _ _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ _ => ko) (fun n t _ => kg n t) (fun _ _ _ => ko) (fun _ _ => kt) l

def LL.mergeHs {α : Sort _} (l : LL) (kh : Nat → LL → α) (kt : α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun _ _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun n t _ => kh n t) (fun _ _ => kt) l

def LL.elimXD {α : Sort _} (l : LL) (kx : Nat → LL → α) (kd : LL → α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun n t _ => kx n t)
    (fun t _ => kd t) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ => ko) l

def LL.elimRC {α : Sort _} (l : LL) (kx : Nat → LL → α) (kd k0 k2 : LL → α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun n t _ => kx n t)
    (fun t _ => kd t) (fun _ _ => ko) (fun t _ => k0 t) (fun _ _ => ko) (fun t _ => k2 t)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ _ => ko)
    (fun _ _ => ko) l

/-- `if b then t else f`, as one recursor step. -/
abbrev bsel {α : Sort _} (b : Bool) (t f : α) : α := Bool.rec (motive := fun _ => α) f t b

/-! ### Left-tape smart constructors -/

def lxNZ (n : Nat) (l : LL) : LL := LL.mergeX l (fun m t => LL.x (Nat.add n m) t) LL.nil (LL.x n l)

def lx (n : Nat) (l : LL) : LL := bsel (Nat.beq n 0) l (lxNZ n l)

def lG (n : Nat) (l : LL) : LL :=
  bsel (Nat.beq n 0) l (LL.mergeGs l (fun m t => LL.Gs (Nat.add n m) t) LL.nil (LL.Gs n l))

def lH (n : Nat) (l : LL) : LL :=
  bsel (Nat.beq n 0) l (LL.mergeHs l (fun m t => LL.Hs (Nat.add n m) t) LL.nil (LL.Hs n l))

/-! ### Right tape (five fields `top tr pc bl tp`; continuations get the new fields) -/

abbrev TK := RL → Nat → Nat → BL → Bool → KS

def kmax (a b : Nat) : Nat := bsel (Nat.ble a b) b a

/-- Push `x n` with `n ≠ 0`. -/
def pushXnz (n : Nat) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  RL.rec (motive := fun _ => KS)
    (k RL.nil (Nat.add tr n) pc bl tp)
    (fun a t _ => k (RL.x (Nat.add a n) t) tr pc bl tp)
    (fun _ _ => k (RL.x n top) tr pc bl tp)
    (fun _ _ _ => k (RL.x n top) tr pc bl tp)
    (fun _ _ => k (RL.x n top) tr pc bl tp)
    top

def pushX (n : Nat) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  bsel (Nat.beq n 0) (k top tr pc bl tp) (pushXnz n top tr pc bl tp k)

def pushG (n : Nat) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  bsel (Nat.beq n 0) (k top tr pc bl tp)
    (RL.rec (motive := fun _ => KS)
      (k (RL.G n top) tr pc bl tp)
      (fun _ _ _ => k (RL.G n top) tr pc bl tp)
      (fun _ _ => k (RL.G n top) tr pc bl tp)
      (fun m t _ => k (RL.G (Nat.add n m) t) tr pc bl tp)
      (fun _ _ => k (RL.G n top) tr pc bl tp)
      top)

def pushP (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  RL.rec (motive := fun _ => KS)
    (bsel (Nat.beq tr 0)
      (BL.rec (motive := fun _ => KS)
        (bsel tp (k (RL.P top) tr (Nat.add pc 1) bl tp) (k top tr pc bl true))
        (fun _ _ _ _ _ _ _ => k (RL.P top) tr (Nat.add pc 1) bl tp) bl)
      (k (RL.P top) tr (Nat.add pc 1) bl tp))
    (fun _ _ _ => k (RL.P top) tr (Nat.add pc 1) bl tp)
    (fun _ _ => k (RL.P top) tr (Nat.add pc 1) bl tp)
    (fun _ _ _ => k (RL.P top) tr (Nat.add pc 1) bl tp)
    (fun _ _ => k (RL.P top) tr (Nat.add pc 1) bl tp)
    top

def pushC (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  k RL.nil 0 0 (BL.cons top tr pc 0 0 bl) tp

def addPend (s r : Nat) (bl : BL) : BL :=
  BL.rec (motive := fun _ => BL) BL.nil
    (fun body btr bpc s' r' rest _ => BL.cons body btr bpc (Nat.add s' s) (kmax r' (Nat.add s' r)) rest)
    bl

/-- Add `s ≠ 0` to the first run of a level (items `body`, trailing run `tr`). -/
def firstAdd (s : Nat) (body : RL) (tr : Nat) (k : RL → Nat → KS) : KS :=
  RL.rec (motive := fun _ => KS)
    (k RL.nil (Nat.add tr s))
    (fun a t _ => k (RL.x (Nat.add a s) t) tr)
    (fun _ _ => k (RL.x s body) tr)
    (fun _ _ _ => k (RL.x s body) tr)
    (fun _ _ => k (RL.x s body) tr)
    body

/-- Materialize the next level, applying its pending summary. -/
def popLevel (body : RL) (btr bpc s r : Nat) (rest : BL) (tp : Bool) (kN : KS) (kC : TK) : KS :=
  bsel (Nat.beq s 0)
    (kC body btr bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp)
    (bsel (Nat.beq bpc 0)
      (BL.rec (motive := fun _ => KS)
        (bsel tp (firstAdd s body btr fun body' btr' => kC body' btr' bpc BL.nil tp) kN)
        (fun _ _ _ _ _ _ _ =>
          RL.rec (motive := fun _ => KS)
            (bsel (Nat.ble r btr)
              (kC RL.nil (Nat.sub btr s) bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp) kN)
            (fun _ _ _ => bsel (Nat.ble (Nat.mul 2 s) btr)
              (firstAdd s body (Nat.sub btr (Nat.mul 2 s)) fun body' btr' =>
                kC body' btr' bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp) kN)
            (fun _ _ => bsel (Nat.ble (Nat.mul 2 s) btr)
              (firstAdd s body (Nat.sub btr (Nat.mul 2 s)) fun body' btr' =>
                kC body' btr' bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp) kN)
            (fun _ _ _ => bsel (Nat.ble (Nat.mul 2 s) btr)
              (firstAdd s body (Nat.sub btr (Nat.mul 2 s)) fun body' btr' =>
                kC body' btr' bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp) kN)
            (fun _ _ => bsel (Nat.ble (Nat.mul 2 s) btr)
              (firstAdd s body (Nat.sub btr (Nat.mul 2 s)) fun body' btr' =>
                kC body' btr' bpc (addPend (Nat.mul 4 s) (Nat.mul 4 r) rest) tp) kN)
            body)
        rest)
      kN)

/-- Pop the head item: `kN` on failure / empty tape, one continuation per kind. -/
def pop (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool)
    (kN : KS) (kX : Nat → TK) (kD kC kP : TK) (kG : Nat → TK) : KS :=
  RL.rec (motive := fun _ => KS)
    (bsel (Nat.beq tr 0)
      (BL.rec (motive := fun _ => KS)
        (bsel tp (kP RL.nil tr pc BL.nil false) kN)
        (fun body btr bpc s r rest _ => popLevel body btr bpc s r rest tp kN kC) bl)
      (kX tr RL.nil 0 pc bl tp))
    (fun a t _ => kX a t tr pc bl tp)
    (fun t _ => kD t tr pc bl tp)
    (fun n t _ => kG n t tr pc bl tp)
    (fun t _ => kP t tr (Nat.sub pc 1) bl tp)
    top

def tick (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  bsel tp
    (bsel (Nat.beq pc 0)
      (BL.rec (motive := fun _ => KS) (k top tr pc bl tp)
        (fun body btr bpc s r rest _ => bsel (Nat.ble 1 tr)
          (k top (Nat.sub tr 1) pc (BL.cons body btr bpc (Nat.add s 2) (kmax r (Nat.add s 4)) rest) true)
          KS.stuck) bl)
      KS.stuck)
    KS.stuck

/-- Expansion of a `G` block (pushed onto the head level). -/
def gexp (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  k (RL.x 299 (RL.D (RL.x 30826 (RL.D (RL.x 72142 (RL.D (RL.x 3076 (RL.D (RL.x 1538 (RL.D top))))))))))
    tr pc bl tp

/-- Peel one `x` off the right tape (expanding a `G` block first). -/
def unx (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  pop top tr pc bl tp KS.stuck
    (fun n top tr pc bl tp => bsel (Nat.beq n 0) KS.stuck (pushX (Nat.sub n 1) top tr pc bl tp k))
    (fun _ _ _ _ _ => KS.stuck) (fun _ _ _ _ _ => KS.stuck) (fun _ _ _ _ _ => KS.stuck)
    (fun n top tr pc bl tp => bsel (Nat.beq n 0) KS.stuck
      (pushG (Nat.sub n 1) top tr pc bl tp fun top tr pc bl tp => gexp top tr pc bl tp k))

/-! ### Left-moving steps (no event code) -/

def lEmpty (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  pop top tr pc bl tp KS.stuck (fun _ _ _ _ _ _ => KS.stuck) (fun _ _ _ _ _ => KS.stuck)
    (fun top tr pc bl tp => unx top tr pc bl tp fun top tr pc bl tp =>
      pushP top tr pc bl tp (KS.R (LL.D (LL.C1 LL.nil))))
    (fun _ _ _ _ _ => KS.stuck) (fun _ _ _ _ _ _ => KS.stuck)

def lF3 (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  LL.elimX l (fun n t => bsel (Nat.beq n 0) KS.stuck
      (KS.R (LL.D (LL.C1 (LL.P (lx (Nat.sub n 1) t)))) top tr pc bl tp))
    KS.stuck

def lstep (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  LL.rec (motive := fun _ => KS)
    (lEmpty top tr pc bl tp)
    (fun n t _ => pushX n top tr pc bl tp (KS.L t))
    (fun t _ => KS.L t (RL.D top) tr pc bl tp)
    (fun t _ => pushP top tr pc bl tp (KS.L t))
    (fun t _ => KS.R (LL.x 1 (LL.C1 t)) top tr pc bl tp)
    (fun t _ => KS.R (LL.C2 t) top tr pc bl tp)
    (fun t _ => KS.R (LL.x 1 (LL.C3 t)) top tr pc bl tp)
    (fun t _ => KS.L t RL.nil 0 0 (BL.cons top tr pc 0 0 bl) tp)
    (fun t _ => KS.R (LL.x 1 (LL.F1 t)) top tr pc bl tp)
    (fun t _ => KS.R (LL.F2 t) top tr pc bl tp)
    (fun t _ => KS.R (LL.x 1 (LL.F3 t)) top tr pc bl tp)
    (fun t _ => lF3 t top tr pc bl tp)
    (fun t _ => KS.R (LL.x 1 (LL.G1 t)) top tr pc bl tp)
    (fun t _ => KS.R (LL.G2 t) top tr pc bl tp)
    (fun t _ => KS.R (LL.x 1 (LL.D (LL.P t))) top tr pc bl tp)
    (fun _ _ _ => KS.stuck)
    (fun n t _ => pushG n top tr pc bl tp (KS.L t))
    (fun _ _ _ => KS.stuck)
    (fun _ _ => KS.stuck)
    l

/-! ### Right-moving simple steps -/

def rEnd (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  LL.elimXD l
    (fun n t => bsel (Nat.beq n 0) KS.stuck
      (pushP top tr pc bl tp fun top tr pc bl tp =>
        pushXnz 1 top tr pc bl tp fun top tr pc bl tp =>
        pushC top tr pc bl tp (KS.L (lx (Nat.sub n 1) t))))
    (fun t => pushXnz 1 top tr pc bl tp (KS.L t))
    KS.stuck

def rC (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  LL.elimRC l
    (fun n t => bsel (Nat.beq n 0) KS.stuck (KS.R (LL.C0 (lx (Nat.sub n 1) t)) top tr pc bl tp))
    (fun t => KS.R (LL.x 1 (LL.P t)) top tr pc bl tp)
    (fun t => KS.R (LL.G0 t) top tr pc bl tp)
    (fun t => KS.R (LL.F0 t) top tr pc bl tp)
    KS.stuck

def rPD3 (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  pop top tr pc bl tp KS.stuck
    (fun n top tr pc bl tp => bsel (Nat.beq n 0) KS.stuck
      (pushX (Nat.sub n 1) top tr pc bl tp fun top tr pc bl tp =>
        pushP top tr pc bl tp (KS.R (LL.D (LL.C1 l)))))
    (fun top tr pc bl tp => unx top tr pc bl tp (KS.R (LL.D (LL.C1 (LL.C2 l)))))
    (fun top tr pc bl tp => unx top tr pc bl tp fun top tr pc bl tp =>
      pushP top tr pc bl tp (KS.R (LL.D (LL.G1 l))))
    (fun top tr pc bl tp => KS.R (LL.D (LL.C1 l)) top tr pc bl tp)
    (fun n top tr pc bl tp => pushP (RL.D top) tr pc bl tp (KS.R (lH n l)))

def rP2 (l : LL) (top0 : RL) (tr0 pc0 : Nat) (bl0 : BL) (tp0 : Bool)
    (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  pop top tr pc bl tp (KS.L l top0 tr0 pc0 bl0 tp0)
    (fun n top tr pc bl tp => pushP top tr pc bl tp (KS.R (lx n l)))
    (fun top tr pc bl tp => rPD3 l top tr pc bl tp)
    (fun top tr pc bl tp => unx top tr pc bl tp fun top tr pc bl tp =>
      pushP top tr pc bl tp fun top tr pc bl tp =>
      pushP (RL.D top) tr pc bl tp (KS.L l))
    (fun top tr pc bl tp => KS.R (lxNZ 1 l) top tr pc bl tp)
    (fun _ _ _ _ _ _ => KS.stuck)

def rItem (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  pop top tr pc bl tp (rEnd l top tr pc bl tp)
    (fun n top tr pc bl tp => KS.R (lxNZ n l) top tr pc bl tp)
    (fun top tr pc bl tp => KS.R (LL.D l) top tr pc bl tp)
    (fun top tr pc bl tp => rC l top tr pc bl tp)
    (fun top' tr' pc' bl' tp' => rP2 l top tr pc bl tp top' tr' pc' bl' tp')
    (fun n top tr pc bl tp => KS.R (lG n l) top tr pc bl tp)

/-- `m` ticks at once (a sweep with multiplier `m`), as `RT.tickN`. -/
def tickN (m : Nat) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) (k : TK) : KS :=
  bsel tp
    (bsel (Nat.beq pc 0)
      (BL.rec (motive := fun _ => KS) (k top tr pc bl tp)
        (fun body btr bpc s r rest _ => bsel (Nat.ble m tr)
          (k top (Nat.sub tr m) pc
            (BL.cons body btr bpc (Nat.add s (Nat.mul 2 m)) (kmax r (Nat.add s (Nat.mul 4 m))) rest) true)
          KS.stuck) bl)
      KS.stuck)
    KS.stuck

/-! ### Universal cycles in constant time -/

/-- Split off the head symbol of a left tape. -/
def LL.uncons {α : Sort _} (l : LL) (k : LS → LL → α) (kn : α) : α :=
  LL.rec (motive := fun _ => α) kn (fun n t _ => k (.x n) t)
    (fun t _ => k .D t) (fun t _ => k .P t) (fun t _ => k .C0 t) (fun t _ => k .C1 t)
    (fun t _ => k .C2 t) (fun t _ => k .C3 t) (fun t _ => k .F0 t) (fun t _ => k .F1 t)
    (fun t _ => k .F2 t) (fun t _ => k .F3 t) (fun t _ => k .G0 t) (fun t _ => k .G1 t)
    (fun t _ => k .G2 t) (fun n t _ => k (.Fs n) t) (fun n t _ => k (.Gs n) t)
    (fun n t _ => k (.Hs n) t) (fun t _ => k .tl t) l

/-- Push a symbol (no merging). -/
def LL.cons (s : LS) (t : LL) : LL :=
  LS.rec (motive := fun _ => LL) (fun n => LL.x n t) (LL.D t) (LL.P t) (LL.C0 t) (LL.C1 t)
    (LL.C2 t) (LL.C3 t) (LL.F0 t) (LL.F1 t) (LL.F2 t) (LL.F3 t) (LL.G0 t) (LL.G1 t) (LL.G2 t)
    (fun n => LL.Fs n t) (fun n => LL.Gs n t) (fun n => LL.Hs n t) (LL.tl t) s

/-- Prepend a constant list of symbols. -/
def LL.prepend (p : List LS) (l : LL) : LL :=
  List.rec (motive := fun _ => LL) l (fun s _ ih => LL.cons s ih) p

/-- Strip a constant prefix `p` (continuation `ok` with the rest), else `ko`. -/
def LL.strip (p : List LS) (l : LL) (ok : LL → KS) (ko : KS) : KS :=
  List.rec (motive := fun _ => LL → (LL → KS) → KS) (fun l ok => ok l)
    (fun s _ ih l ok => LL.uncons l (fun h t => bsel (s == h) (ih t ok) ko) ko) p l ok

def LL.mergeFs {α : Sort _} (l : LL) (kf : Nat → LL → α) (kt : α) (ko : α) : α :=
  LL.rec (motive := fun _ => α) ko (fun _ _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko) (fun _ _ => ko)
    (fun _ _ => ko) (fun n t _ => kf n t) (fun _ _ _ => ko) (fun _ _ _ => ko) (fun _ _ => kt) l

def lF (n : Nat) (l : LL) : LL :=
  bsel (Nat.beq n 0) l (LL.mergeFs l (fun m t => LL.Fs (Nat.add n m) t) LL.nil (LL.Fs n l))

/-- `k` universal cycles at once (`uniKSt lazyOps k`): constant work, the
right tape gets one batched lazy sweep. -/
def uniK (k : Nat) (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool) : KS :=
  LL.uncons l (fun s1 l1 => bsel (s1 == .D)
    (LL.uncons l1 (fun s2 l2 => bsel (s2 == .C1)
      (LL.elimX l2 (fun a l3 =>
        LL.strip Jc l3 (fun l4 =>
          bsel (Nat.blt 0 k && Nat.blt (Nat.mul k uniP) a)
            (tickN (Nat.mul k uniT) top tr pc bl tp fun top tr pc bl tp =>
              pushG k top tr pc bl tp fun top tr pc bl tp =>
                KS.R (LL.D (LL.C1 (LL.x (Nat.sub a (Nat.mul k uniP)) (LL.prepend Jc (lF k l4)))))
                  top tr pc bl tp)
            KS.stuck) KS.stuck)
        KS.stuck)
      KS.stuck) KS.stuck)
    KS.stuck) KS.stuck

/-- Right-moving event: code `0` simple step, `1` tick, otherwise `k` universal
cycles with `k` the next entry of `ks`.  `kont` receives the remaining `ks`. -/
def rstep (e : Nat) (ks : List Nat) (l : LL) (top : RL) (tr pc : Nat) (bl : BL) (tp : Bool)
    (kont : List Nat → KS → KS) : KS :=
  bsel (Nat.beq e 0) (kont ks (rItem l top tr pc bl tp))
    (bsel (Nat.beq e 1) (kont ks (tick top tr pc bl tp (KS.L l)))
      (List.rec (motive := fun _ => KS) KS.stuck
        (fun k ks' _ => kont ks' (uniK k l top tr pc bl tp)) ks))

/-- Run `n` events of one group: `codes` holds the codes of its right-moving
events (two bits each, least significant first, at most 32 of them), `ks` the
numbers of cycles of its universal-cycle events. -/
def runN (n : Nat) : Nat → List Nat → KS → KS :=
  Nat.rec (motive := fun _ => Nat → List Nat → KS → KS)
    (fun _ _ c => c)
    (fun _ ih codes ks c => KS.rec (motive := fun _ => KS)
      (fun l top tr pc bl tp => ih codes ks (lstep l top tr pc bl tp))
      (fun l top tr pc bl tp => rstep (Nat.mod codes 4) ks l top tr pc bl tp (ih (Nat.div codes 4)))
      KS.stuck c)
    n

/-- Run a list of groups `(number of events, codes, cycle counts)`. -/
def runL (gs : List (Nat × Nat × List Nat)) : KS → KS :=
  List.rec (motive := fun _ => KS → KS) (fun c => c)
    (fun g _ ih c => ih (runN g.1 g.2.1 g.2.2 c)) gs

end

/-- Does a left tape contain the abstract tail marker? -/
def hasTl : List LS → Bool
  | [] => false
  | .tl :: _ => true
  | _ :: l => hasTl l

/-- Gluing check between the final left tape `b` of one segment and the initial
left tape `a` of the next one: `a` is `b` truncated (a prefix of `b` followed by
the tail marker), or `a = b`. -/
def glueL : List LS → List LS → Bool
  | _, [.tl] => true
  | x :: b, y :: a => x == y && glueL b a
  | [], [] => true
  | _, _ => false

/-- Equality test for lazy configurations. -/
def St.beqR (c d : St RT) : Bool := c.right == d.right && c.l == d.l && c.r == d.r

/-- The check of one certificate segment: the grouped run from the lazy
configuration `c0` ends exactly in `c1`, and the tail marker (if any) survives. -/
noncomputable def checkS (gs : List (Nat × Nat × List Nat)) (c0 c1 : St RT) : Bool :=
  (!hasTl c0.l || hasTl c1.l) &&
    match (runL gs (KS.ofSt c0)).toSt with
    | some c => St.beqR c c1
    | none => false

end Sk1.K4

