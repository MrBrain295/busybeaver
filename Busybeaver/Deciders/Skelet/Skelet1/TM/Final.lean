import Busybeaver.Deciders.Skelet.Skelet1.TM.Simple
import Busybeaver.Deciders.Skelet.Skelet1.TM.SweepAlg
import Busybeaver.Deciders.Skelet.Skelet1.TM.UniCycle
import Busybeaver.Deciders.Skelet.Skelet1.Cert.Frame

/-!
# From the symbolic run to non-halting of the machine

* every event of the eager symbolic simulator is a machine run between the lifted
  configurations (`step_sound`), hence so is every symbolic run (`steps_sound`);
* the blank tape reaches the lift of the simulator's initial configuration (`init_reaches`);
* the cycle configurations `⟨true, C0 :: Y, Kc⟩` form a family closed under machine
  progress (`cycle_progress`), so none of them halts;
* hence a symbolic run from `init` to a cycle configuration proves that the machine
  never halts (`nonhalt_of_reaches_cycle`).
-/

namespace Sk1.TM

open Turing

theorem tick_sound {c c' : St (List RI)} (h : tickSt eagerOps c = some c') :
    Reaches (lift c) (lift c') := by
  obtain ⟨right, l, r⟩ := c
  cases right
  · simp [tickSt] at h
  · simp only [tickSt, ite_true] at h
    cases hs : sweep 0 1 r with
    | none => simp [eagerOps, hs] at h
    | some r' =>
      simp only [eagerOps, hs, Option.map_some, Option.some.injEq] at h
      subst c'
      simpa only [lift_right, lift_left] using sweep_sound hs

/-! ### Simple steps and ticks -/

theorem step0_sound {c c' : St (List RI)} (h : Step0 c c') (htl : LS.tl ∉ c.l) :
    Reaches (lift c) (lift c') := by
  rcases h with h | h
  · exact simple_sound h htl
  · obtain ⟨d, l, r⟩ := c
    cases d
    · simp [tickSt] at h
    · simp only [tickSt, ite_true] at h
      cases hr : sweep 0 1 r with
      | none => simp [eagerOps, hr] at h
      | some r' =>
        simp only [eagerOps, hr, Option.map_some, Option.some.injEq] at h
        subst h
        have ht : tickSt eagerOps ⟨true, l, r⟩ = some ⟨false, l, r'⟩ := by
          simp [tickSt, eagerOps, hr]
        exact tick_sound ht

theorem step0_tl {c c' : St (List RI)} (h : Step0 c c') (htl : LS.tl ∉ c.l) : LS.tl ∉ c'.l := by
  intro h'
  rcases h with h | h
  · exact htl (simple_frame eagerOps [] h h').1
  · exact htl (tickSt_frame eagerOps [] h h').1

theorem steps0_sound {c c' : St (List RI)} (h : Relation.ReflTransGen Step0 c c')
    (htl : LS.tl ∉ c.l) : Reaches (lift c) (lift c') ∧ LS.tl ∉ c'.l := by
  induction h with
  | refl => exact ⟨Reaches.refl _, htl⟩
  | tail _ hs ih => exact ⟨ih.1.trans (step0_sound hs ih.2), step0_tl hs ih.2⟩

/-! ### Universal cycles -/

theorem liftL_append (a b : List LS) : liftL (a ++ b) = (a.flatMap LS.blk) +> liftL b := by
  induction a with
  | nil => rfl
  | cons s a ih => simp [ih, append_append]

theorem tl_not_mem_lF {n : Nat} {l : List LS} (hl : LS.tl ∉ l) : LS.tl ∉ lF n l := by
  unfold lF
  split_ifs
  · exact hl
  · split <;> simp_all

/-- The left part of a cycle configuration. -/
def pre (a : Nat) : List LS := .D :: .C1 :: .x a :: Jc

theorem tl_not_mem_pre (a : Nat) : LS.tl ∉ pre a := by simp [pre, Jc]

/-- One universal cycle as a machine run. -/
theorem uni_one (m : Nat) (l : List LS) (hl : LS.tl ∉ l) {r r' : List RI}
    (h : sweep 0 uniT r = some r') :
    Reaches (dR (liftL (pre (m + uniP + 1) ++ l)) (liftR r))
      (dR ((pre (m + 1)).flatMap LS.blk +> bpow FlB 1 +> liftL l) (bpow GrB 1 +> liftR r')) := by
  have hs := steps0_sound (uni_cycle_steps m l h)
    (by simp [tl_not_mem_Jc, hl])
  have e1 : liftL (.D :: .C1 :: .x (m + 1) :: Jc ++ ([.x 10344, .D, .x 7640, .C2] ++ l)) =
      (pre (m + 1)).flatMap LS.blk +> bpow FlB 1 +> liftL l := by
    rw [show (LS.D :: .C1 :: .x (m + 1) :: Jc ++ ([.x 10344, .D, .x 7640, .C2] ++ l)) =
      pre (m + 1) ++ ([.x 10344, .D, .x 7640, .C2] ++ l) from rfl, liftL_append, liftL_append]
    simp only [bpow_one, FlB, List.flatMap_cons, List.flatMap_nil, LS.blk, List.append_nil,
      List.append_assoc]
  have e2 : liftR ([.x 300, .D, .x 30826, .D, .x 72142, .D, .x 3076, .D, .x 1538, .D] ++ r') =
      bpow GrB 1 +> liftR r' := by
    simp only [bpow_one, GrB, List.cons_append, List.nil_append, liftR_cons, RI.blk,
      append_append, List.append_assoc]
  have := hs.1
  simp only [lift_right] at this
  rw [e1, e2] at this
  exact this

/-- `k + 1` universal cycles as a machine run. -/
theorem uni_k (k : Nat) : ∀ (m : Nat) (l : List LS), LS.tl ∉ l → ∀ {r r' : List RI},
    sweep 0 ((k + 1) * uniT) r = some r' →
    Reaches (dR (liftL (pre (m + (k + 1) * uniP + 1) ++ l)) (liftR r))
      (dR ((pre (m + 1)).flatMap LS.blk +> bpow FlB (k + 1) +> liftL l)
        (bpow GrB (k + 1) +> liftR r')) := by
  induction k with
  | zero =>
    intro m l hl r r' h
    have := uni_one m l hl (r := r) (by rwa [Nat.zero_add, Nat.one_mul] at h)
    rwa [show m + (0 + 1) * uniP + 1 = m + uniP + 1 by ring]
  | succ k ih =>
    intro m l hl r r' h
    rw [show (k + 1 + 1) * uniT = (k + 1) * uniT + uniT by ring] at h
    obtain ⟨r1, h1, h2⟩ := sw_add_gen r 0 ((k + 1) * uniT) uniT r' h
    have hA := ih (m + uniP) l hl h1
    rw [show m + uniP + (k + 1) * uniP + 1 = m + (k + 1 + 1) * uniP + 1 by ring] at hA
    have hpG := sweep_pushG 0 (k + 1) uniT (by omega) r1
    rw [h2] at hpG
    simp only [pushX_zero] at hpG
    have hB := uni_one m (lF (k + 1) l) (tl_not_mem_lF hl) hpG
    rw [liftL_append, liftL_lF _ _ hl, liftR_pushG, liftR_pushG] at hB
    refine hA.trans ?_
    have e1 : bpow FlB (k + 1 + 1) = bpow FlB 1 ++ bpow FlB (k + 1) := by
      rw [← bpow_add, Nat.add_comm 1]
    have e2 : bpow GrB (k + 1 + 1) = bpow GrB 1 ++ bpow GrB (k + 1) := by
      rw [← bpow_add, Nat.add_comm 1]
    rw [e1, e2, ← append_append, ← append_append]
    exact hB

/-- The universal cycles of the simulator (with any admissible count `k`) are machine runs. -/
theorem uni_core {a k : Nat} {l : List LS} {r r'' : List RI} (hl : LS.tl ∉ l) (hk : 0 < k)
    (ha : k * uniP < a) (h : sweep 0 (k * uniT) r = some r'') :
    Reaches (lift ⟨true, .D :: .C1 :: .x a :: Jc ++ l, r⟩)
      (dR (liftL (.D :: .C1 :: .x (a - k * uniP) :: Jc ++ lF k l)) (bpow GrB k +> liftR r'')) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  simp only [Nat.zero_add] at *
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt ha
  have := uni_k k m l hl h
  rw [show (k + 1) * uniP + m + 1 = m + (k + 1) * uniP + 1 by ring]
  rw [show m + (k + 1) * uniP + 1 - (k + 1) * uniP = m + 1 by omega]
  have e : (LS.D :: .C1 :: .x (m + (k + 1) * uniP + 1) :: Jc ++ l) =
    pre (m + (k + 1) * uniP + 1) ++ l := rfl
  have e' : (LS.D :: .C1 :: .x (m + 1) :: Jc ++ lF (k + 1) l) = pre (m + 1) ++ lF (k + 1) l := rfl
  simp only [lift_right]
  rw [e, e', liftL_append, liftL_append, liftL_lF _ _ hl]
  rw [liftL_append] at this
  exact this

theorem uniKSt_sound {k : Nat} {c c' : St (List RI)} (h : uniKSt eagerOps k c = some c')
    (htl : LS.tl ∉ c.l) : Reaches (lift c) (lift c') := by
  obtain ⟨d, l0, r⟩ := c
  unfold uniKSt at h
  cases d
  · simp at h
  simp only [ite_true] at h
  split at h
  · rename_i a l1 hl0
    split at h
    · rename_i l hs
      have hl1 := stripP_eq hs
      subst hl1
      split_ifs at h with hk
      cases hsw : eagerOps.tickN (k * uniT) r with
      | none => simp [hsw] at h
      | some r'' =>
        simp only [hsw, Option.some.injEq] at h
        subst h
        have hl : LS.tl ∉ l := fun h' => htl (by simp [h'])
        have := uni_core hl hk.1 hk.2 (r := r) (r'' := r'') hsw
        simpa [liftR_push, RI.blk] using this
    · cases h
  · cases h

theorem liftR_ofList (t : List RI) : liftR (eagerOps.ofList t) = liftR t := by
  induction t with
  | nil => rfl
  | cons i t ih =>
    show liftR (ePush (eagerOps.ofList t) i) = _
    rw [liftR_ePush, ih]; rfl

theorem uniCount_lt {a k : Nat} {t : List RI} (h : uniCount a t = k + 1) :
    (k + 1) * uniP < a := by
  unfold uniCount at h
  by_cases h0 : (a - 1) / uniP = 0
  · simp only [h0, ↓reduceIte] at h; omega
  · simp only [h0, ↓reduceIte] at h
    have hle : k + 1 ≤ (a - 1) / uniP := by
      split at h
      · rw [← h]; exact Nat.min_le_left _ _
      · omega
    have h1 : (k + 1) * uniP ≤ (a - 1) / uniP * uniP := Nat.mul_le_mul_right _ hle
    have h2 : (a - 1) / uniP * uniP ≤ a - 1 := Nat.div_mul_le_self _ _
    have h3 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; simp at h0
      · exact ha
    omega

theorem uniSt_sound {c c' : St (List RI)} (h : uniSt eagerOps c = some c')
    (htl : LS.tl ∉ c.l) : Reaches (lift c) (lift c') := by
  obtain ⟨d, l0, r⟩ := c
  unfold uniSt at h
  cases d
  · simp at h
  simp only [ite_true] at h
  split at h
  · rename_i a l1 hl0
    split at h
    · rename_i l hs
      have hl1 := stripP_eq hs
      subst hl1
      simp only [eagerOps] at h
      split at h
      · cases h
      · rename_i k hk
        cases hsw : sweep 0 ((k + 1) * uniT) r with
        | none => simp [hsw] at h
        | some r'' =>
          simp only [hsw, Option.some.injEq] at h
          subst h
          have hl : LS.tl ∉ l := fun h' => htl (by simp [h'])
          have := uni_core hl (Nat.succ_pos k) (uniCount_lt hk) (r := r) (r'' := r'') hsw
          have e := liftR_ofList (pushG (k + 1) r'')
          simp only [eagerOps] at e
          simp only [lift_right, e, liftR_pushG]
          simpa using this
    · cases h
  · cases h

/-! ### Events and runs -/

theorem step_sound {c c' : St (List RI)} (h : Step eagerOps c c') (htl : LS.tl ∉ c.l) :
    Reaches (lift c) (lift c') := by
  rcases h with ⟨e, he⟩
  match e, he with
  | 0, he =>
    have hs : simple eagerOps c = some c' := by
      simpa [ev] using he
    exact simple_sound hs htl
  | 1, he => exact step0_sound (Or.inr he) htl
  | _ + 2, he => exact uniSt_sound he htl

theorem steps_sound {c c' : St (List RI)} (h : Steps eagerOps c c') (htl : LS.tl ∉ c.l) :
    Reaches (lift c) (lift c') := by
  induction h with
  | refl => exact Reaches.refl _
  | tail hs hst ih =>
    exact ih.trans (step_sound hst (fun h' => htl (steps_tl eagerOps hs h')))

/-! ### The start -/

theorem init_reaches : Reaches TM.init (lift Sk1.init) := by
  have h := wreach_sound (n := 19) (s := W.st .A (List.replicate 10 false) (List.replicate 10 false))
    (t := W.st .A (C1B ++ List.replicate 7 false) (PB ++ List.replicate 4 false)) (by decide) ∅ ∅
  have e1 : (W.st .A (List.replicate 10 false) (List.replicate 10 false)).den ∅ ∅ = TM.init := by
    simp only [W.den, TM.init]
    rw [show List.replicate 10 false = [] ++ List.replicate 10 false from rfl, append_blanks]
    rfl
  have e2 : (W.st .A (C1B ++ List.replicate 7 false) (PB ++ List.replicate 4 false)).den ∅ ∅ =
      lift Sk1.init := by
    simp only [W.den, Sk1.init, lift_right, liftL_cons, liftL_nil, liftR_cons, liftR_nil,
      append_blanks, LS.blk, RI.blk]
    rfl
  rw [e1, e2] at h
  exact h

/-! ### The terminal cycle -/

/-- Tick if possible, else a simple step (the event choice of the accelerated simulator). -/
def autoStep (c : St (List RI)) : Option (St (List RI)) :=
  match tickSt eagerOps c with
  | some c' => some c'
  | none => simple eagerOps c

def autoN : Nat → St (List RI) → Option (St (List RI))
  | 0, c => some c
  | n + 1, c => match autoStep c with
    | some c' => autoN n c'
    | none => none

theorem autoStep_step {c c' : St (List RI)} (h : autoStep c = some c') : Step eagerOps c c' := by
  unfold autoStep at h
  split at h
  · rename_i c1 h1
    cases h
    exact ⟨1, h1⟩
  · exact ⟨0, by simpa [ev] using h⟩

theorem autoN_steps (n : Nat) {c c' : St (List RI)} (h : autoN n c = some c') :
    Steps eagerOps c c' := by
  induction n generalizing c with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [autoN] at h
    split at h
    · rename_i c1 h1
      exact Relation.ReflTransGen.head (autoStep_step h1) (ih h)
    · cases h

def St.beqE (c d : St (List RI)) : Bool := c.right == d.right && c.l == d.l && c.r == d.r

theorem St.beqE_eq {c d : St (List RI)} (h : St.beqE c d = true) : c = d := by
  obtain ⟨d1, l1, r1⟩ := c
  obtain ⟨d2, l2, r2⟩ := d
  simp only [St.beqE, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

/-- The `F` block that one pass of the terminal cycle adds to the left tape. -/
def Fc : List LS := [.x 10344, .D, .x 7640, .C2]

def cyc0 : St (List RI) := ⟨true, [.C0, .tl], Kc⟩
def cyc1 : St (List RI) := ⟨true, .C0 :: Fc ++ [.tl], Kc⟩

/-- One pass of the terminal cycle, checked by evaluation: 30 events to a left-moving
configuration, then 952 more events back to the cycle shape with `Fc` added. -/
def cycCheck : Bool :=
  match autoN 30 cyc0 with
  | some mid => !mid.right && LS.tl ∈ mid.l && match autoN 952 mid with
    | some c => St.beqE c cyc1
    | none => false
  | none => false

theorem cycCheck_true : cycCheck = true := by decide +kernel

theorem cycle_progress (Y : List LS) (hY : LS.tl ∉ Y) :
    Reaches1 (lift ⟨true, .C0 :: Y, Kc⟩) (lift ⟨true, .C0 :: (Fc ++ Y), Kc⟩) := by
  have h := cycCheck_true
  unfold cycCheck at h
  split at h
  · rename_i mid hmid
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨hr, htm⟩, h2⟩ := h
    split at h2
    · rename_i c hc
      have hce := St.beqE_eq h2
      subst hce
      have s1 := steps_frame (autoN_steps 30 hmid) Y (fun _ => htm)
      have s2 := steps_frame (autoN_steps 952 hc) Y (fun _ => by simp [cyc1, Fc])
      simp only [cyc0, cyc1, Fc, substT, List.cons_append, List.nil_append] at s1 s2
      have hY0 : LS.tl ∉ (LS.C0 :: Y) := by simp [hY]
      have t1 := steps_sound s1 (by simpa [substT] using hY0)
      have t2 := steps_sound s2 (fun h' => by
        have := steps_tl eagerOps s1 h'
        simp at this
        exact hY this)
      have hq : (lift ⟨true, LS.C0 :: Y, Kc⟩).q ≠ (lift ⟨mid.right, substT Y mid.l, mid.r⟩).q := by
        simp [hr, lift, dR, dL]
      exact (t1.reaches1_of_q_ne hq).trans_reaches t2
    · cases h2
  · cases h

/-- **Non-halting from the symbolic run.**  If the symbolic simulator gets from `init` to
a cycle configuration, the Skelet #1 machine started on the blank tape never halts. -/
theorem nonhalt_of_reaches_cycle (h : ∃ Y, Steps eagerOps Sk1.init ⟨true, .C0 :: Y, Kc⟩) :
    ¬ Halts TM.init := by
  obtain ⟨Y, hs⟩ := h
  have hY : LS.tl ∉ Y := fun h' => by
    have := steps_tl eagerOps hs (List.mem_cons_of_mem _ h')
    simp [Sk1.init] at this
  have hr := init_reaches.trans (steps_sound hs (by simp [Sk1.init]))
  refine not_halts_of_reaches hr ?_
  refine not_halts_of_closed (fun c => ∃ Y, LS.tl ∉ Y ∧ c = lift ⟨true, .C0 :: Y, Kc⟩) ?_ _
    ⟨Y, hY, rfl⟩
  rintro c ⟨Y, hY, rfl⟩
  refine ⟨_, ⟨Fc ++ Y, ?_, rfl⟩, cycle_progress Y hY⟩
  simp [Fc, hY]

end Sk1.TM
