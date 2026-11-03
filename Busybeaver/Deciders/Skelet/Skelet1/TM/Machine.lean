import Mathlib.Computability.TuringMachine.Tape
import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-!
# The Skelet #1 Turing machine and the meaning of symbolic configurations

* `M` is the machine `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC` (five states, two
  symbols, `E` reading `0` is the undefined transition).
* `Cfg` is a machine configuration over Mathlib's `Turing.Tape Bool` (blank `false`).
* `Halts c` : some number of steps from `c` reaches a configuration without a transition.
* `lift` gives the meaning of a symbolic configuration `St (List RI)`: every left
  symbol `LS` and right item `RI` stands for a fixed block of cells.

The window runner `wstep`/`wreach` is a small verified executable model of the
machine on a finite piece of tape; `wreach_sound` turns a successful window run
into a machine run with arbitrary tape contents outside the window.  Finite
rule lemmas are proved with it by `decide`.
-/

namespace Sk1.TM

open Turing

inductive Q | A | B | C | D | E
  deriving DecidableEq, Repr

/-- Skelet #1: `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC`. -/
def M : Q → Bool → Option (Bool × Dir × Q)
  | .A, false => some (true, .right, .B)
  | .A, true => some (true, .right, .D)
  | .B, false => some (true, .left, .C)
  | .B, true => some (false, .right, .C)
  | .C, false => some (true, .right, .A)
  | .C, true => some (true, .left, .D)
  | .D, false => some (false, .right, .E)
  | .D, true => some (false, .left, .B)
  | .E, false => none
  | .E, true => some (true, .right, .C)

structure Cfg where
  q : Q
  T : Tape Bool

/-- One machine step (`none` if the transition is undefined). -/
def step (c : Cfg) : Option Cfg :=
  match M c.q c.T.head with
  | none => none
  | some (b, d, q') => some ⟨q', (c.T.write b).move d⟩

/-- `n` machine steps. -/
def stepN : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c => match step c with
    | none => none
    | some c' => stepN n c'

/-- The initial configuration: state `A` on the blank tape. -/
def init : Cfg := ⟨.A, Tape.mk' ∅ ∅⟩

/-- The machine halts from `c`: after some number of steps no transition applies. -/
def Halts (c : Cfg) : Prop := ∃ n, stepN n c = none

def StepRel (a b : Cfg) : Prop := step a = some b

/-- Finitely many machine steps. -/
def Reaches : Cfg → Cfg → Prop := Relation.ReflTransGen StepRel

/-- At least one machine step. -/
def Reaches1 : Cfg → Cfg → Prop := Relation.TransGen StepRel

theorem Reaches.trans {a b c : Cfg} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c :=
  Relation.ReflTransGen.trans h1 h2

theorem Reaches.refl (a : Cfg) : Reaches a a := Relation.ReflTransGen.refl

theorem stepN_add (m n : ℕ) (c : Cfg) :
    stepN (m + n) c = (stepN m c).bind (stepN n) := by
  induction m generalizing c with
  | zero => simp [stepN]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [stepN]
    cases step c with
    | none => rfl
    | some c' => exact ih c'

theorem Reaches.exists_stepN {a b : Cfg} (h : Reaches a b) : ∃ n, stepN n a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [stepN_add, hn]
    have hs' : step _ = some _ := hs
    simp [stepN, hs']

theorem Reaches1.exists_stepN {a b : Cfg} (h : Reaches1 a b) : ∃ n, stepN (n + 1) a = some b := by
  induction h with
  | single hs =>
    have hs' : step _ = some _ := hs
    exact ⟨0, by simp [stepN, hs']⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    have hs' : step _ = some _ := hs
    rw [stepN_add, hn]
    simp [stepN, hs']

theorem Reaches.reaches1_of_q_ne {a b : Cfg} (h : Reaches a b) (hq : a.q ≠ b.q) : Reaches1 a b := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hac, hcb⟩
  · subst h; exact absurd rfl hq
  · exact Relation.TransGen.head' hac hcb

theorem Reaches1.trans_reaches {a b c : Cfg} (h1 : Reaches1 a b) (h2 : Reaches b c) :
    Reaches1 a c := Relation.TransGen.trans_left h1 h2

theorem Reaches.trans_reaches1 {a b c : Cfg} (h1 : Reaches a b) (h2 : Reaches1 b c) :
    Reaches1 a c := Relation.TransGen.trans_right h1 h2

theorem Reaches1.reaches {a b : Cfg} (h : Reaches1 a b) : Reaches a b := h.to_reflTransGen

/-- If every configuration of a family makes progress to another member of the
family, no member halts. -/
theorem not_halts_of_closed (S : Cfg → Prop) (hS : ∀ c, S c → ∃ c', S c' ∧ Reaches1 c c') :
    ∀ c, S c → ¬ Halts c := by
  intro c hc ⟨n, hn⟩
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    obtain ⟨c', hc', hr⟩ := hS c hc
    obtain ⟨m, hm⟩ := hr.exists_stepN
    by_cases hle : n ≤ m + 1
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, stepN_add, hn] at hm
      simp at hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le hle)
      rw [show m + 1 + k + 1 = (m + 1) + (k + 1) by omega, stepN_add, hm] at hn
      exact ih (k + 1) (by omega) c' hc' hn

/-- Non-halting is inherited backwards along runs. -/
theorem not_halts_of_reaches {a b : Cfg} (h : Reaches a b) (hb : ¬ Halts b) : ¬ Halts a := by
  intro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := h.exists_stepN
  apply hb
  by_cases hle : n ≤ m
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, stepN_add, hn] at hm
    simp at hm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_not_le hle)
    rw [show m + k + 1 = m + (k + 1) by omega, stepN_add, hm] at hn
    exact ⟨k + 1, hn⟩

/-! ## Blocks -/

/-- `1ⁿ0`. -/
def run (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- `n` copies of a block. -/
def bpow (b : List Bool) (n : ℕ) : List Bool := (List.replicate n b).flatten

def xB : List Bool := run 2 ++ run 2
def DlB : List Bool := run 1 ++ run 2
def DrB : List Bool := run 2 ++ run 1
def PB : List Bool := run 2
def C0B : List Bool := run 2 ++ run 3 ++ run 2
def C1B : List Bool := run 1 ++ run 0 ++ run 2
def C2B : List Bool := run 2 ++ run 4
def C3B : List Bool := run 1 ++ run 1
def F0B : List Bool := run 2 ++ run 3 ++ run 4
def F1B : List Bool := run 1 ++ run 0 ++ run 4
def F2B : List Bool := run 2 ++ run 6
def F3B : List Bool := run 1 ++ run 3
def G0B : List Bool := run 2 ++ run 3 ++ run 3 ++ run 2
def G1B : List Bool := run 1 ++ run 0 ++ run 3 ++ run 2
def G2B : List Bool := run 2 ++ run 5 ++ run 2

/-- The right block of one `G` (right orientation). -/
def GrB : List Bool :=
  bpow xB 300 ++ DrB ++ bpow xB 30826 ++ DrB ++ bpow xB 72142 ++ DrB ++
    bpow xB 3076 ++ DrB ++ bpow xB 1538 ++ DrB

/-- The left block of one `Gs` (the mirror of `GrB`). -/
def GlB : List Bool :=
  DlB ++ bpow xB 1538 ++ DlB ++ bpow xB 3076 ++ DlB ++ bpow xB 72142 ++ DlB ++
    bpow xB 30826 ++ DlB ++ bpow xB 300

/-- The left block of one `Hs`. -/
def HlB : List Bool :=
  bpow xB 1537 ++ DlB ++ C1B ++ bpow xB 3075 ++ DlB ++ C1B ++ bpow xB 72141 ++ DlB ++ C1B ++
    bpow xB 30825 ++ DlB ++ C1B ++ bpow xB 299 ++ DlB ++ C1B

/-- The left block of one `Fs`. -/
def FlB : List Bool := bpow xB 10344 ++ DlB ++ bpow xB 7640 ++ C2B

/-- Cells of a left symbol, head-nearest first.  (`tl` is only a proof device and
never occurs in configurations that are lifted.) -/
def _root_.Sk1.LS.blk : LS → List Bool
  | .x n => bpow xB n
  | .D => DlB
  | .P => PB
  | .C0 => C0B
  | .C1 => C1B
  | .C2 => C2B
  | .C3 => C3B
  | .F0 => F0B
  | .F1 => F1B
  | .F2 => F2B
  | .F3 => F3B
  | .G0 => G0B
  | .G1 => G1B
  | .G2 => G2B
  | .Fs n => bpow FlB n
  | .Gs n => bpow GlB n
  | .Hs n => bpow HlB n
  | .tl => []

/-- Cells of a right item, head-nearest first. -/
def _root_.Sk1.RI.blk : RI → List Bool
  | .x n => bpow xB n
  | .D => DrB
  | .C => C3B
  | .P => PB
  | .G n => bpow GrB n

/-- `b +> L`: the cells `b` (head-nearest first) in front of the half-tape `L`. -/
scoped infixr:67 " +> " => ListBlank.append

def liftL : List LS → ListBlank Bool
  | [] => ∅
  | s :: l => s.blk +> liftL l

def liftR : List RI → ListBlank Bool
  | [] => ∅
  | i :: r => i.blk +> liftR r

/-- Right-moving configuration: state `A` reading the first cell of the right side. -/
def dR (L R : ListBlank Bool) : Cfg := ⟨.A, Tape.mk' L R⟩

/-- Left-moving configuration: state `C` reading the first cell of the left side,
with the two cells `1 0` between the head and the right side. -/
def dL (L R : ListBlank Bool) : Cfg :=
  ⟨.C, (Tape.mk' L ([true, false] +> R)).move .left⟩

/-- The machine configuration a symbolic configuration stands for. -/
def lift (c : St (List RI)) : Cfg :=
  if c.right then dR (liftL c.l) (liftR c.r) else dL (liftL c.l) (liftR c.r)

@[simp] theorem lift_right (l : List LS) (r : List RI) :
    lift ⟨true, l, r⟩ = dR (liftL l) (liftR r) := rfl

@[simp] theorem lift_left (l : List LS) (r : List RI) :
    lift ⟨false, l, r⟩ = dL (liftL l) (liftR r) := rfl

@[simp] theorem liftL_nil : liftL [] = ∅ := rfl
@[simp] theorem liftL_cons (s : LS) (l : List LS) : liftL (s :: l) = s.blk +> liftL l := rfl
@[simp] theorem liftR_nil : liftR [] = ∅ := rfl
@[simp] theorem liftR_cons (i : RI) (r : List RI) : liftR (i :: r) = i.blk +> liftR r := rfl

/-! ## Window runs

A window state lists the cells near the head that a finite computation may
read: `st q L R` has the head on `R`'s first cell (`L` head-nearest first).
`exitL q R` is the state just after the head moved left out of the window onto
the unknown left side. -/

inductive W
  | st (q : Q) (L R : List Bool)
  | exitL (q : Q) (R : List Bool)
  deriving DecidableEq

/-- The machine configuration of a window state with half-tapes `TL`, `TR` outside. -/
def W.den (TL TR : ListBlank Bool) : W → Cfg
  | .st q L R => ⟨q, Tape.mk' (L +> TL) (R +> TR)⟩
  | .exitL q R => ⟨q, (Tape.mk' TL (R +> TR)).move .left⟩

/-- One window step; `none` if the step would read outside the window. -/
def wstep : W → Option W
  | .st q L (b :: R) =>
    match M q b with
    | none => none
    | some (w, .right, q') => some (.st q' (w :: L) R)
    | some (w, .left, q') =>
      match L with
      | a :: L' => some (.st q' L' (a :: w :: R))
      | [] => some (.exitL q' (w :: R))
  | _ => none

theorem wstep_sound {s s' : W} (h : wstep s = some s') (TL TR : ListBlank Bool) :
    step (s.den TL TR) = some (s'.den TL TR) := by
  match s, h with
  | .st q L (b :: R), h =>
    simp only [wstep] at h
    simp only [W.den, step, Tape.mk'_head, ListBlank.append, ListBlank.head_cons]
    cases hM : M q b with
    | none => rw [hM] at h; cases h
    | some t =>
      obtain ⟨w, d, q'⟩ := t
      rw [hM] at h
      cases d with
      | right =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [Option.some.injEq, Cfg.mk.injEq, true_and]
        simp [Tape.mk', Tape.write, Tape.move, ListBlank.append, ListBlank.tail_cons]
      | left =>
        cases L with
        | cons a L' =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Option.some.injEq, Cfg.mk.injEq, true_and]
          simp [Tape.mk', Tape.write, Tape.move, ListBlank.append, ListBlank.tail_cons,
            ListBlank.head_cons]
        | nil =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Option.some.injEq, Cfg.mk.injEq, true_and]
          simp [Tape.mk', Tape.write, Tape.move, ListBlank.append, ListBlank.tail_cons,
            ListBlank.head_cons]

/-- Does the window run from `s` reach `t` within `n` steps? -/
def wreach : ℕ → W → W → Bool
  | 0, s, t => s == t
  | n + 1, s, t => s == t || match wstep s with
    | some s' => wreach n s' t
    | none => false

theorem wreach_sound {n : ℕ} {s t : W} (h : wreach n s t = true) (TL TR : ListBlank Bool) :
    Reaches (s.den TL TR) (t.den TL TR) := by
  induction n generalizing s with
  | zero =>
    simp only [wreach, beq_iff_eq] at h
    subst h; exact Reaches.refl _
  | succ n ih =>
    simp only [wreach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact Reaches.refl _
    · split at h
      · rename_i s' hs
        exact Relation.ReflTransGen.head (wstep_sound hs TL TR) (ih h)
      · cases h

/-! ### Basic facts about half-tapes -/

theorem append_append (a b : List Bool) (L : ListBlank Bool) : a +> b +> L = (a ++ b) +> L :=
  (ListBlank.append_assoc a b L).symm

@[simp] theorem nil_append (L : ListBlank Bool) : [] +> L = L := rfl

theorem cons_append (a : Bool) (b : List Bool) (L : ListBlank Bool) :
    (a :: b) +> L = (b +> L).cons a := rfl

/-- Blank cells in front of the empty half-tape can be dropped. -/
theorem append_blanks (b : List Bool) (k : ℕ) :
    (b ++ List.replicate k false) +> (∅ : ListBlank Bool) = b +> ∅ := by
  have h1 : (∅ : ListBlank Bool) = ListBlank.mk [] := rfl
  rw [h1, ListBlank.append_mk, ListBlank.append_mk, List.append_nil, List.append_nil]
  exact Quot.sound (Or.inr ⟨k, rfl⟩)

theorem bpow_zero (b : List Bool) : bpow b 0 = [] := rfl

theorem bpow_succ (b : List Bool) (n : ℕ) : bpow b (n + 1) = b ++ bpow b n := by
  simp [bpow, List.replicate_succ]

theorem bpow_add (b : List Bool) (m n : ℕ) : bpow b (m + n) = bpow b m ++ bpow b n := by
  rw [bpow, bpow, bpow, List.replicate_add, List.flatten_append]

theorem bpow_succ' (b : List Bool) (n : ℕ) : bpow b (n + 1) = bpow b n ++ b := by
  rw [bpow_add]; simp [bpow]

theorem bpow_one (b : List Bool) : bpow b 1 = b := by simp [bpow]

/-! ### Configurations as window states -/

theorem dR_eq_den (a b : List Bool) (L R : ListBlank Bool) :
    dR (a +> L) (b +> R) = (W.st .A a b).den L R := rfl

theorem dL_eq_exitL (L R : ListBlank Bool) :
    dL L R = (W.exitL .C [true, false]).den L R := rfl

theorem dL_cons_eq_den (b0 : Bool) (bs : List Bool) (L R : ListBlank Bool) :
    dL ((b0 :: bs) +> L) R = (W.st .C bs [b0, true, false]).den L R := by
  simp only [dL, W.den, Tape.move_left_mk', cons_append, ListBlank.tail_cons,
    ListBlank.head_cons]

theorem exitL_den (q : Q) (R0 : List Bool) (L R : ListBlank Bool) :
    (W.exitL q R0).den L R = ⟨q, (Tape.mk' L (R0 +> R)).move .left⟩ := rfl

/-- A left-moving configuration whose right side starts with known cells. -/
theorem dL_append_eq_exitL (b : List Bool) (L R : ListBlank Bool) :
    dL L (b +> R) = (W.exitL .C ([true, false] ++ b)).den L R := by
  simp only [dL, W.den, append_append]

end Sk1.TM
