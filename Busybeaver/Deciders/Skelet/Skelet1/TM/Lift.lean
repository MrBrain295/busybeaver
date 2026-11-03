import Busybeaver.Deciders.Skelet.Skelet1.TM.Machine

/-!
# Lifts of the simulator's tape operations

The merging pushes of the symbolic simulator only change how a tape is written,
not the cells it stands for.
-/

namespace Sk1.TM

open Turing

theorem liftL_lx (n : Nat) (l : List LS) (hl : LS.tl ∉ l) :
    liftL (lx n l) = bpow xB n +> liftL l := by
  unfold lx
  split_ifs with h
  · subst h; rfl
  · split
    · simp [LS.blk, bpow_add, append_append]
    · simp at hl
    · rfl

theorem liftL_lF (n : Nat) (l : List LS) (hl : LS.tl ∉ l) :
    liftL (lF n l) = bpow FlB n +> liftL l := by
  unfold lF
  split_ifs with h
  · subst h; rfl
  · split
    · simp [LS.blk, bpow_add, append_append]
    · simp at hl
    · rfl

theorem liftL_lG (n : Nat) (l : List LS) (hl : LS.tl ∉ l) :
    liftL (lG n l) = bpow GlB n +> liftL l := by
  unfold lG
  split_ifs with h
  · subst h; rfl
  · split
    · simp [LS.blk, bpow_add, append_append]
    · simp at hl
    · rfl

theorem liftL_lH (n : Nat) (l : List LS) (hl : LS.tl ∉ l) :
    liftL (lH n l) = bpow HlB n +> liftL l := by
  unfold lH
  split_ifs with h
  · subst h; rfl
  · split
    · simp [LS.blk, bpow_add, append_append]
    · simp at hl
    · rfl

theorem liftR_pushX (n : Nat) (t : List RI) : liftR (pushX n t) = bpow xB n +> liftR t := by
  unfold pushX
  split_ifs with h
  · subst h; rfl
  · split
    · simp [RI.blk, bpow_add, append_append]
    · rfl

theorem liftR_pushG (n : Nat) (t : List RI) : liftR (pushG n t) = bpow GrB n +> liftR t := by
  unfold pushG
  split_ifs with h
  · subst h; rfl
  · split
    · simp [RI.blk, bpow_add, append_append]
    · rfl

theorem liftR_ePush (t : List RI) (i : RI) : liftR (ePush t i) = i.blk +> liftR t := by
  cases i <;> simp [ePush, liftR_pushX, liftR_pushG, RI.blk]

theorem liftR_push (t : List RI) (i : RI) : liftR (eagerOps.push t i) = i.blk +> liftR t :=
  liftR_ePush t i

theorem GrB_eq : GrB = xB ++ (bpow xB 299 ++ DrB ++ bpow xB 30826 ++ DrB ++ bpow xB 72142 ++
    DrB ++ bpow xB 3076 ++ DrB ++ bpow xB 1538 ++ DrB) := by
  simp only [GrB, List.append_assoc]
  rw [show (300 : ℕ) = 299 + 1 from rfl, bpow_succ, List.append_assoc]

/-- Peeling one `x` (expanding a `G` block if needed) does not change the cells. -/
theorem liftR_unx {t t' : List RI} (h : unx eagerOps t = some t') : liftR t = xB +> liftR t' := by
  unfold unx at h
  split at h
  · rename_i n t0 hp
    simp only [eagerOps] at hp
    split at hp
    · cases hp
    · rename_i i t1
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [Option.some.injEq] at h
      subst h
      simp [liftR_push, RI.blk, bpow_succ, append_append]
  · rename_i n t0 hp
    simp only [eagerOps] at hp
    split at hp
    · cases hp
    · rename_i i t1
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.foldr, liftR_push, append_append]
      simp only [liftR_cons, RI.blk]
      rw [bpow_succ GrB n]
      nth_rewrite 1 [GrB_eq]
      simp only [List.append_assoc]
  · cases h

end Sk1.TM
