import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Correct
import Busybeaver.Deciders.Skelet.Skelet1.TM.Rules
import Busybeaver.TuringExt

/-!
# Pure algebra of the eager sweep

Facts about `sweep` used by the machine-level soundness of a tick:

* `sw_acc`: an extra accumulated run in front of a successful sweep is just pushed
  in front of the result;
* `sw_add_gen`: a sweep with multiplier `n + m` splits into a sweep with multiplier
  `n` followed by a sweep with multiplier `m`;
* `sw_four`: the four sweeps of the rest of the tape made by the machine during a
  carry over a `C` compose to one sweep with multiplier `4`;
* `sw_countC`: sweeps preserve the number of `C` items.
-/

namespace Sk1.TM

open Turing
open scoped Sk1.TM

theorem sw_x (a n b : Nat) (t : List RI) : sweep a n (.x b :: t) = sweep (a + b) n t := by
  simp [sweep]

theorem sw_G (a n g : Nat) (t : List RI) :
    sweep a n (.G g :: t) = (sweep 0 n t).map fun t => pushX a (pushG g t) := by
  simp [sweep]

theorem sw_nil (a n : Nat) : sweep a n [] = none := by simp [sweep]

theorem pushG_zero' (t : List RI) : pushG 0 t = t := by simp [pushG]

/-- An extra accumulated run is pushed in front of the result. -/
theorem sw_acc : ∀ (t : List RI) (a c m : Nat) (u : List RI),
    sweep c m t = some u → sweep (a + c) m t = some (pushX a u)
  | [], a, c, m, u, h => by simp [sw_nil] at h
  | [.P], a, c, m, u, h => by
    rw [sweep_Pend] at h
    rw [sweep_Pend]
    cases h
    rw [pushX_pushX]
  | .P :: i :: t, a, c, m, u, h => by
    rw [sweep_P _ _ _ (List.cons_ne_nil _ _)] at h; cases h
  | .x b :: t, a, c, m, u, h => by
    rw [sw_x] at h
    rw [sw_x, Nat.add_assoc]
    exact sw_acc t a (c + b) m u h
  | .D :: t, a, c, m, u, h => by
    rw [sweep_D] at h
    rw [sweep_D]
    cases h' : sweep 0 m t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      rw [← h, pushX_pushX]
  | .G g :: t, a, c, m, u, h => by
    rw [sw_G] at h
    rw [sw_G]
    cases h' : sweep 0 m t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      rw [← h, pushX_pushX]
  | .C :: t, a, c, m, u, h => by
    rw [sweep_C] at h
    rw [sweep_C]
    split_ifs at h with hc
    cases h' : sweep 0 (4 * m) t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [show m ≤ a + c from by omega, ↓reduceIte, Option.map_some, Option.some.injEq]
      rw [← h, pushX_pushX]
      congr 1
      omega

/-- A sweep with multiplier `n + m` is a sweep with multiplier `n` followed by a
sweep with multiplier `m`. -/
theorem sw_add_gen : ∀ (t : List RI) (a n m : Nat) (t2 : List RI),
    sweep a (n + m) t = some t2 → ∃ t1, sweep a n t = some t1 ∧ sweep 0 m t1 = some t2
  | [], a, n, m, t2, h => by simp [sw_nil] at h
  | [.P], a, n, m, t2, h => by
    rw [sweep_Pend] at h
    cases h
    refine ⟨pushX a [.P], sweep_Pend _ _, ?_⟩
    rw [sweep_pushX, sweep_Pend, Nat.zero_add]
  | .P :: i :: t, a, n, m, t2, h => by
    rw [sweep_P _ _ _ (List.cons_ne_nil _ _)] at h; cases h
  | .x b :: t, a, n, m, t2, h => by
    rw [sw_x] at h
    rw [sw_x]
    exact sw_add_gen t (a + b) n m t2 h
  | .D :: t, a, n, m, t2, h => by
    rw [sweep_D] at h
    cases h' : sweep 0 (n + m) t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨t1, h1, h2⟩ := sw_add_gen t 0 n m v h'
      refine ⟨pushX a (.D :: t1), ?_, ?_⟩
      · rw [sweep_D, h1]; rfl
      · rw [sweep_pushX, sweep_D, h2, Nat.zero_add, ← h]; rfl
  | .G g :: t, a, n, m, t2, h => by
    rw [sw_G] at h
    cases h' : sweep 0 (n + m) t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨t1, h1, h2⟩ := sw_add_gen t 0 n m v h'
      refine ⟨pushX a (pushG g t1), ?_, ?_⟩
      · rw [sw_G, h1]; rfl
      · rw [sweep_pushX, Nat.zero_add, ← h]
        by_cases hg : g = 0
        · subst hg
          rw [pushG_zero', pushG_zero']
          have := sw_acc t1 a 0 m v h2
          rwa [Nat.add_zero] at this
        · rw [sweep_pushG _ _ _ hg, h2]; rfl
  | .C :: t, a, n, m, t2, h => by
    rw [sweep_C] at h
    split_ifs at h with hc
    cases h' : sweep 0 (4 * (n + m)) t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [Nat.mul_add] at h'
      obtain ⟨t1, h1, h2⟩ := sw_add_gen t 0 (4 * n) (4 * m) v h'
      refine ⟨pushX (a - n) (.C :: pushX (2 * n) t1), ?_, ?_⟩
      · rw [sweep_C, h1]; simp only [show n ≤ a from by omega, ↓reduceIte, Option.map_some]
      · rw [sweep_pushX, sweep_C, Nat.zero_add, sweep_pushX, Nat.zero_add]
        simp only [show m ≤ a - n from by omega, ↓reduceIte]
        have h3 := sw_acc t1 (2 * n) 0 (4 * m) v h2
        rw [Nat.add_zero] at h3
        rw [h3, ← h]
        simp only [Option.map_some, pushX_pushX]
        rw [show a - n - m = a - (n + m) by omega, show 2 * m + 2 * n = 2 * (n + m) by omega]

/-- The four sweeps of a carry compose to one sweep with multiplier `4`. -/
theorem sw_four {t u : List RI} (h : sweep 0 4 t = some u) :
    ∃ t1 t2 t3, sweep 0 1 t = some t1 ∧ sweep 1 1 t1 = some t2 ∧ sweep 0 1 t2 = some t3 ∧
      sweep 1 1 t3 = some (pushX 2 u) := by
  obtain ⟨s1, h1, h1'⟩ := sw_add_gen t 0 1 3 u h
  obtain ⟨s2, h2, h2'⟩ := sw_add_gen s1 0 1 2 u h1'
  obtain ⟨s3, h3, h4⟩ := sw_add_gen s2 0 1 1 u h2'
  refine ⟨s1, pushX 1 s2, pushX 1 s3, h1, sw_acc s1 1 0 1 s2 h2, ?_, ?_⟩
  · rw [sweep_pushX, Nat.zero_add]
    exact sw_acc s2 1 0 1 s3 h3
  · rw [sweep_pushX]
    exact sw_acc s3 2 0 1 u h4

/-! ### Number of `C` items -/

def countC : List RI → Nat
  | [] => 0
  | .C :: t => countC t + 1
  | _ :: t => countC t

theorem countC_pushX (n : Nat) (t : List RI) : countC (pushX n t) = countC t := by
  unfold pushX
  split_ifs
  · rfl
  · split <;> simp [countC]

theorem countC_pushG (n : Nat) (t : List RI) : countC (pushG n t) = countC t := by
  unfold pushG
  split_ifs
  · rfl
  · split <;> simp [countC]

theorem sw_countC : ∀ (t : List RI) (a n : Nat) (u : List RI),
    sweep a n t = some u → countC u = countC t
  | [], a, n, u, h => by simp [sw_nil] at h
  | [.P], a, n, u, h => by
    rw [sweep_Pend] at h
    cases h
    rw [countC_pushX]
  | .P :: i :: t, a, n, u, h => by
    rw [sweep_P _ _ _ (List.cons_ne_nil _ _)] at h; cases h
  | .x b :: t, a, n, u, h => by
    rw [sw_x] at h
    rw [sw_countC t _ _ u h]; rfl
  | .D :: t, a, n, u, h => by
    rw [sweep_D] at h
    cases h' : sweep 0 n t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h, countC_pushX]
      simp [countC, sw_countC t _ _ v h']
  | .G g :: t, a, n, u, h => by
    rw [sw_G] at h
    cases h' : sweep 0 n t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h, countC_pushX, countC_pushG]
      simp [countC, sw_countC t _ _ v h']
  | .C :: t, a, n, u, h => by
    rw [sweep_C] at h
    split_ifs at h with hc
    cases h' : sweep 0 (4 * n) t with
    | none => rw [h'] at h; cases h
    | some v =>
      rw [h'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h, countC_pushX, countC, countC, countC_pushX, sw_countC t _ _ v h']

private abbrev SweepStmt (t : List RI) (k : Nat) : Prop :=
  ∀ (t' : List RI) (a : Nat) (l : ListBlank Bool),
    countC t = k → sweep a 1 t = some t' →
      Reaches (dR (bpow xB a +> l) (liftR t)) (dL l (liftR t'))

private theorem sweep_case_x (t : List RI) (IH : SweepStmt t k)
    (t' : List RI) (a b : Nat) (l : ListBlank Bool)
    (hcnt : countC t = k) (h : sweep a 1 (.x b :: t) = some t') :
    Reaches (dR (bpow xB a +> l) (liftR (.x b :: t))) (dL l (liftR t')) := by
  simp only [sweep] at h
  simp only [liftR, RI.blk]
  refine (r_xn b (bpow xB a +> l) (liftR t)).trans ?_
  rw [append_append, ← bpow_add, Nat.add_comm b a]
  exact IH t' (a + b) l hcnt h

private theorem sweep_case_D (t : List RI) (IH : SweepStmt t k)
    (t' : List RI) (a : Nat) (l : ListBlank Bool)
    (hcnt : countC t = k) (h : sweep a 1 (.D :: t) = some t') :
    Reaches (dR (bpow xB a +> l) (liftR (.D :: t))) (dL l (liftR t')) := by
  simp only [sweep] at h
  cases hs : sweep 0 1 t with
  | none => simp [hs] at h
  | some t1 =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst t'
    simp only [liftR, RI.blk]
    refine (r_D (bpow xB a +> l) (liftR t)).trans ?_
    have hmid := IH t1 0 (DlB +> (bpow xB a +> l)) hcnt hs
    simp only [bpow_zero, ListBlank.append_empty] at hmid
    refine hmid.trans ?_
    refine (l_D (bpow xB a +> l) (liftR t1)).trans ?_
    simpa only [liftR_pushX, liftR, RI.blk, ListBlank.append_assoc'] using
      l_xn a l (DrB +> liftR t1)

private theorem sweep_case_G (t : List RI) (IH : SweepStmt t k)
    (t' : List RI) (a g : Nat) (l : ListBlank Bool)
    (hcnt : countC t = k) (h : sweep a 1 (.G g :: t) = some t') :
    Reaches (dR (bpow xB a +> l) (liftR (.G g :: t))) (dL l (liftR t')) := by
  simp only [sweep] at h
  cases hs : sweep 0 1 t with
  | none => simp [hs] at h
  | some t1 =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    subst t'
    simp only [liftR, RI.blk]
    refine (r_G g (bpow xB a +> l) (liftR t)).trans ?_
    have hmid := IH t1 0 (bpow GlB g +> (bpow xB a +> l)) hcnt hs
    simp only [bpow_zero, ListBlank.append_empty] at hmid
    refine hmid.trans ?_
    refine (l_Gs g (bpow xB a +> l) (liftR t1)).trans ?_
    simpa only [liftR_pushX, liftR_pushG, ListBlank.append_assoc'] using
      l_xn a l (bpow GrB g +> liftR t1)

private theorem sweep_case_P (t : List RI)
    (t' : List RI) (a : Nat) (l : ListBlank Bool)
    (h : sweep a 1 (.P :: t) = some t') :
    Reaches (dR (bpow xB a +> l) (liftR (.P :: t))) (dL l (liftR t')) := by
  cases t with
  | nil =>
    simp only [sweep, Option.some.injEq] at h
    subst t'
    simp only [liftR, RI.blk]
    refine (r_P_end (bpow xB a +> l)).trans ?_
    simpa only [liftR_pushX, liftR, RI.blk, ListBlank.append_assoc'] using
      l_xn a l (PB +> ∅)
  | cons i t => simp [sweep] at h

private theorem sweep_correct' (k : Nat) :
    ∀ (t t' : List RI) (a : Nat) (l : ListBlank Bool),
      countC t = k → sweep a 1 t = some t' →
        Reaches (dR (bpow xB a +> l) (liftR t)) (dL l (liftR t')) := by
  induction k with
  | zero =>
    intro t
    induction t with
    | nil => intro t' a l hc h; simp [sweep] at h
    | cons i t IHt =>
      intro t' a l hc h
      cases i with
      | x b =>
        have hc' : countC t = 0 := by simpa [countC] using hc
        exact sweep_case_x t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a b l hc' h
      | D =>
        have hc' : countC t = 0 := by simpa [countC] using hc
        exact sweep_case_D t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a l hc' h
      | G g =>
        have hc' : countC t = 0 := by simpa [countC] using hc
        exact sweep_case_G t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a g l hc' h
      | P => exact sweep_case_P t t' a l h
      | C => simp [countC] at hc
  | succ k ih =>
    intro t
    induction t with
    | nil => intro t' a l hc h; simp [sweep] at h
    | cons i t IHt =>
      intro t' a l hc h
      cases i with
      | x b =>
        have hc' : countC t = k + 1 := by simpa [countC] using hc
        exact sweep_case_x t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a b l hc' h
      | D =>
        have hc' : countC t = k + 1 := by simpa [countC] using hc
        exact sweep_case_D t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a l hc' h
      | G g =>
        have hc' : countC t = k + 1 := by simpa [countC] using hc
        exact sweep_case_G t (fun t' a l _ h => IHt t' a l (by simpa [countC] using hc') h)
          t' a g l hc' h
      | P => exact sweep_case_P t t' a l h
      | C =>
        have hcnt : countC t = k := by simp only [countC] at hc; omega
        simp only [sweep] at h
        split at h
        · rename_i hle
          cases hs : sweep 0 4 t with
          | none => simp [hs] at h
          | some tfin =>
            simp only [hs, Option.map_some, Option.some.injEq] at h
            subst t'
            simp only [liftR, RI.blk, Nat.mul_one]
            obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 := ⟨a - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            rw [bpow_succ, ListBlank.append_assoc]
            refine (r_C_x (bpow xB u +> l) (liftR t)).trans ?_
            have hE : sweep 0 4 t = some tfin := hs
            rw [show (4 : Nat) = 1 + 3 by rfl] at hE
            obtain ⟨t1, h1, hE⟩ := sw_add_gen t 0 1 3 tfin hE
            have r1 := ih t t1 0 (C0B +> (bpow xB u +> l)) hcnt h1
            simp only [bpow_zero, ListBlank.append_empty] at r1
            refine r1.trans ?_
            refine (l_C0 (bpow xB u +> l) (liftR t1)).trans ?_
            rw [show (3 : Nat) = 1 + 2 by rfl] at hE
            obtain ⟨t2, h2, hE⟩ := sw_add_gen t1 0 1 2 tfin hE
            have hcnt1 : countC t1 = k := (sw_countC t 0 1 t1 h1).trans hcnt
            have r2 := ih t1 t2 0 (xB +> C1B +> (bpow xB u +> l)) hcnt1 h2
            simp only [bpow_zero, ListBlank.append_empty] at r2
            refine r2.trans ?_
            refine (l_xn 1 (C1B +> (bpow xB u +> l)) (liftR t2)).trans ?_
            refine (l_C1 (bpow xB u +> l) (xB +> liftR t2)).trans ?_
            refine (r_xn 1 (C2B +> (bpow xB u +> l)) (liftR t2)).trans ?_
            rw [show (2 : Nat) = 1 + 1 by rfl] at hE
            obtain ⟨t3, h3, hE⟩ := sw_add_gen t2 0 1 1 tfin hE
            have hcnt2 : countC t2 = k := (sw_countC t1 0 1 t2 h2).trans hcnt1
            have r3 := ih t2 t3 0 (xB +> C2B +> (bpow xB u +> l)) hcnt2 h3
            simp only [bpow_zero, ListBlank.append_empty] at r3
            refine r3.trans ?_
            refine (l_xn 1 (C2B +> (bpow xB u +> l)) (liftR t3)).trans ?_
            refine (l_C2 (bpow xB u +> l) (xB +> liftR t3)).trans ?_
            refine (r_xn 1 (xB +> C3B +> (bpow xB u +> l)) (liftR t3)).trans ?_
            have hcnt3 : countC t3 = k := (sw_countC t2 0 1 t3 h3).trans hcnt2
            have r4 := ih t3 tfin 0 (xB +> (xB +> C3B +> (bpow xB u +> l))) hcnt3 hE
            simp only [bpow_zero, ListBlank.append_empty] at r4
            refine r4.trans ?_
            refine (l_xn 1 (xB +> C3B +> (bpow xB u +> l)) (liftR tfin)).trans ?_
            refine (l_xn 1 (C3B +> (bpow xB u +> l)) (xB +> liftR tfin)).trans ?_
            refine (l_C3 (bpow xB u +> l) (xB +> (xB +> liftR tfin))).trans ?_
            refine (l_xn u l (C3B +> (xB +> (xB +> liftR tfin)))).trans ?_
            simp only [show (2 : Nat) = 1 + 1 by rfl, liftR_cons, RI.blk,
              liftR_pushX, bpow_succ, bpow_one, bpow_zero, append_append,
              List.append_nil, List.append_assoc]
            exact Reaches.refl _
        · simp at h

/-- One eager sweep is a real machine run from the right-moving to the
left-moving symbolic configuration. -/
theorem sweep_sound {t t' : List RI} {l : List LS}
    (h : sweep 0 1 t = some t') :
    Reaches (dR (liftL l) (liftR t)) (dL (liftL l) (liftR t')) := by
  exact sweep_correct' (countC t) t t' 0 (liftL l) rfl h

end Sk1.TM
