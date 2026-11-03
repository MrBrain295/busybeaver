import Busybeaver.Deciders.Skelet.Skelet1.TM.Rules

/-! # Soundness of the simple symbolic steps -/

namespace Sk1.TM

open Turing

namespace SimpleAux

theorem pop_nil : eagerOps.pop [] = none := rfl
theorem pop_cons (i : RI) (t : List RI) : eagerOps.pop (i :: t) = some (i, t) := rfl
theorem push_eq (t : List RI) (i : RI) : eagerOps.push t i = ePush t i := rfl

attribute [local simp] pop_nil pop_cons push_eq

theorem tl_tail {s : LS} {l : List LS} (h : LS.tl ∉ s :: l) : LS.tl ∉ l :=
  fun hm => h (List.mem_cons_of_mem _ hm)

theorem right_nil {l : List LS} {c' : St (List RI)}
    (h : simple eagerOps ⟨true, l, []⟩ = some c') (htl : LS.tl ∉ l) :
    Reaches (dR (liftL l) ∅) (lift c') := by
  rcases l with _ | ⟨s, l⟩
  · simp [simple] at h
  · have htl' := tl_tail htl
    cases s <;> simp [simple] at h
    · rename_i n
      cases n with
      | zero => simp at h
      | succ n =>
        simp at h
        subst h
        simp only [lift_left, liftR_ePush, liftL_lx _ _ htl', liftL_cons, liftR_nil, RI.blk,
          LS.blk, bpow_one]
        rw [bpow_succ]
        simpa only [append_append, List.append_assoc] using r_end_x (bpow xB n +> liftL l)
    · subst h
      simp only [lift_left, liftR_ePush, liftL_cons, liftR_nil, RI.blk, LS.blk, bpow_one]
      exact r_end_D _

theorem right_C {l : List LS} {r : List RI} {c' : St (List RI)}
    (h : simple eagerOps ⟨true, l, .C :: r⟩ = some c') (htl : LS.tl ∉ l) :
    Reaches (dR (liftL l) (C3B +> liftR r)) (lift c') := by
  rcases l with _ | ⟨s, l⟩
  · simp [simple] at h
  · have htl' := tl_tail htl
    cases s <;> simp [simple] at h
    · rename_i n
      cases n with
      | zero => simp at h
      | succ n =>
        simp at h
        subst h
        simp only [lift_right, liftL_lx _ _ htl', liftL_cons, LS.blk]
        rw [bpow_succ, ← append_append]
        exact r_C_x _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using r_C_D (liftL l) (liftR r)
    · subst h
      exact r_C_C0 _ _
    · subst h
      exact r_C_C2 _ _

theorem right_P {l : List LS} {r : List RI} {c' : St (List RI)}
    (h : simple eagerOps ⟨true, l, .P :: r⟩ = some c') (htl : LS.tl ∉ l) :
    Reaches (dR (liftL l) (PB +> liftR r)) (lift c') := by
  rcases r with _ | ⟨j, r⟩
  · simp [simple] at h
    subst h
    exact r_P_end _
  · cases j with
    | x n =>
      simp [simple] at h
      subst h
      simp only [lift_right, liftL_lx _ _ htl, liftR_ePush, liftR_cons, RI.blk]
      simpa only [append_append] using r_P_xn n (liftL l) (liftR r)
    | D =>
      rcases r with _ | ⟨k, r⟩
      · simp [simple] at h
      · cases k with
        | x n =>
          cases n with
          | zero => simp [simple] at h
          | succ n =>
            simp [simple] at h
            subst h
            simp only [lift_right, liftL_cons, liftR_ePush, liftR_cons, RI.blk, LS.blk]
            rw [bpow_succ]
            simpa only [append_append, List.append_assoc] using
              r_P_D_x (liftL l) (bpow xB n +> liftR r)
        | D =>
          simp [simple] at h
          obtain ⟨r4, hu, rfl⟩ := h
          simp only [lift_right, liftL_cons, liftR_cons, RI.blk, LS.blk, liftR_unx hu]
          simpa only [append_append, List.append_assoc] using r_P_D_D (liftL l) (liftR r4)
        | C =>
          simp [simple] at h
          obtain ⟨r4, hu, rfl⟩ := h
          simp only [lift_right, liftL_cons, liftR_cons, liftR_ePush, RI.blk, LS.blk,
            liftR_unx hu]
          simpa only [append_append, List.append_assoc] using r_P_D_C (liftL l) (liftR r4)
        | P =>
          simp [simple] at h
          subst h
          simp only [lift_right, liftL_cons, liftR_cons, RI.blk, LS.blk]
          simpa only [append_append, List.append_assoc] using r_P_D_P (liftL l) (liftR r)
        | G n =>
          simp [simple] at h
          subst h
          simp only [lift_right, liftL_lH _ _ htl, liftR_cons, liftR_ePush, RI.blk]
          simpa only [append_append, List.append_assoc] using r_P_D_G n (liftL l) (liftR r)
    | C =>
      simp [simple] at h
      obtain ⟨r3, hu, rfl⟩ := h
      simp only [lift_left, liftR_cons, liftR_ePush, RI.blk, liftR_unx hu]
      simpa only [append_append, List.append_assoc] using r_P_C (liftL l) (liftR r3)
    | P =>
      simp [simple] at h
      subst h
      simp only [lift_right, liftL_lx _ _ htl, liftR_cons, RI.blk, bpow_one]
      simpa only [append_append, List.append_assoc] using r_P_P (liftL l) (liftR r)
    | G n =>
      simp [simple] at h

theorem right_cons {l : List LS} {i : RI} {r : List RI} {c' : St (List RI)}
    (h : simple eagerOps ⟨true, l, i :: r⟩ = some c') (htl : LS.tl ∉ l) :
    Reaches (dR (liftL l) (i.blk +> liftR r)) (lift c') := by
  cases i with
  | x n =>
    simp [simple] at h
    subst h
    simp only [lift_right, liftL_lx _ _ htl, RI.blk]
    exact r_xn n _ _
  | D =>
    simp [simple] at h
    subst h
    simp only [lift_right, liftL_cons, RI.blk, LS.blk]
    exact r_D _ _
  | C => exact right_C h htl
  | P => exact right_P h htl
  | G n =>
    simp [simple] at h
    subst h
    simp only [lift_right, liftL_lG _ _ htl, RI.blk]
    exact r_G n _ _

theorem left {l : List LS} {r : List RI} {c' : St (List RI)}
    (h : simple eagerOps ⟨false, l, r⟩ = some c') (htl : LS.tl ∉ l) :
    Reaches (dL (liftL l) (liftR r)) (lift c') := by
  rcases l with _ | ⟨s, l⟩
  · rcases r with _ | ⟨i, r⟩
    · simp [simple] at h
    · cases i <;> simp [simple] at h
      obtain ⟨r', hu, rfl⟩ := h
      simp only [lift_right, liftL_cons, liftL_nil, liftR_cons, liftR_ePush, RI.blk, LS.blk,
        liftR_unx hu]
      simpa only [append_append, List.append_assoc] using l_nil_C (liftR r')
  · have htl' := tl_tail htl
    cases s <;> simp [simple] at h
    · subst h
      simp only [lift_left, liftL_cons, liftR_ePush, LS.blk, RI.blk]
      exact l_xn _ _ _
    · subst h
      simp only [lift_left, liftL_cons, liftR_ePush, LS.blk, RI.blk]
      exact l_D _ _
    · subst h
      simp only [lift_left, liftL_cons, liftR_ePush, LS.blk, RI.blk]
      exact l_P _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using l_C0 (liftL l) (liftR r)
    · subst h
      exact l_C1 _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using l_C2 (liftL l) (liftR r)
    · subst h
      simp only [lift_left, liftL_cons, liftR_ePush, LS.blk, RI.blk]
      exact l_C3 _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using l_F0 (liftL l) (liftR r)
    · subst h
      exact l_F1 _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using l_F2 (liftL l) (liftR r)
    · rcases l with _ | ⟨s2, l⟩
      · simp at h
      · have htl'' := tl_tail htl'
        cases s2 with
        | x n =>
          cases n with
          | zero => simp at h
          | succ n =>
            simp at h
            subst h
            simp only [lift_right, liftL_cons, liftL_lx _ _ htl'', LS.blk]
            rw [bpow_succ]
            simpa only [append_append, List.append_assoc] using
              l_F3 (bpow xB n +> liftL l) (liftR r)
        | _ => simp at h
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append] using l_G0 (liftL l) (liftR r)
    · subst h
      exact l_G1 _ _
    · subst h
      simp only [lift_right, liftL_cons, LS.blk, bpow_one]
      simpa only [append_append, List.append_assoc] using l_G2 (liftL l) (liftR r)
    · subst h
      simp only [lift_left, liftL_cons, liftR_ePush, LS.blk, RI.blk]
      exact l_Gs _ _ _

end SimpleAux

/-- Every simple step of the (eager) symbolic simulator is a machine run between the
lifted configurations. -/
theorem simple_sound {c c' : St (List RI)} (h : simple eagerOps c = some c')
    (htl : LS.tl ∉ c.l) : Reaches (lift c) (lift c') := by
  obtain ⟨right, l, r⟩ := c
  cases right with
  | true =>
    rcases r with _ | ⟨i, r⟩
    · exact SimpleAux.right_nil h htl
    · exact SimpleAux.right_cons h htl
  | false => exact SimpleAux.left h htl

end Sk1.TM
