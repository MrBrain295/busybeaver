import Busybeaver.Deciders.Skelet.Skelet1.TM.RulesAux

/-!
# Machine-level rules

Each lemma is a machine run between two configurations given by blocks in front
of arbitrary half-tapes `L` (left of the head) and `R` (right of the head).
`dR L R`: state `A`, head on the first cell of `R`.  `dL L R`: state `C`, head on
the first cell of `L`, cells `1 0` between the head and `R`.

The `r_*` lemmas start right-moving, the `l_*` lemmas left-moving; each one is the
machine meaning of one case of the symbolic simulator's `simple`.
-/

namespace Sk1.TM

open Turing RulesAux

/-! ### Right-moving -/

theorem r_end_x (L : ListBlank Bool) :
    Reaches (dR (xB +> L) ∅) (dL L ((C3B ++ xB ++ PB) +> ∅)) := by
  refine wreach_cfg (n := 200) (s := W.st .A xB (List.replicate 12 false))
    (t := W.exitL .C ([true, false] ++ ((C3B ++ xB ++ PB) ++ List.replicate 3 false)))
    (by decide) L ∅ ?_ ?_
  · show dR (xB +> L) (List.replicate 12 false +> ∅) = _
    rw [← empty_eq_blanks]
  · rw [← append_blanks (C3B ++ xB ++ PB) 3, dL_den']

theorem r_end_D (L : ListBlank Bool) : Reaches (dR (DlB +> L) ∅) (dL L (xB +> ∅)) := by
  refine wreach_cfg (n := 200) (s := W.st .A DlB (List.replicate 8 false))
    (t := W.exitL .C ([true, false] ++ (xB ++ List.replicate 5 false)))
    (by decide) L ∅ ?_ ?_
  · show dR (DlB +> L) (List.replicate 8 false +> ∅) = _
    rw [← empty_eq_blanks]
  · rw [← append_blanks xB 5, dL_den']

theorem RulesAux.x_right (L R : ListBlank Bool) : Reaches (dR L (xB +> R)) (dR (xB +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A [] xB) (t := W.st .A xB []) (by decide) L R

theorem r_xn (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dR L (bpow xB n +> R)) (dR (bpow xB n +> L) R) := by
  induction n generalizing L with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : bpow xB (n + 1) +> R = xB +> bpow xB n +> R := by rw [bpow_succ, append_append]
    have h2 : bpow xB (n + 1) +> L = bpow xB n +> xB +> L := by rw [bpow_succ', append_append]
    rw [h1, h2]
    exact (x_right L _).trans (ih _)

theorem r_D (L R : ListBlank Bool) : Reaches (dR L (DrB +> R)) (dR (DlB +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A [] DrB) (t := W.st .A DlB []) (by decide) L R

theorem r_C_x (L R : ListBlank Bool) : Reaches (dR (xB +> L) (C3B +> R)) (dR (C0B +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A xB C3B) (t := W.st .A C0B []) (by decide) L R

theorem r_C_D (L R : ListBlank Bool) :
    Reaches (dR (DlB +> L) (C3B +> R)) (dR ((xB ++ PB) +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A DlB C3B) (t := W.st .A (xB ++ PB) []) (by decide) L R

theorem r_C_C0 (L R : ListBlank Bool) : Reaches (dR (C0B +> L) (C3B +> R)) (dR (G0B +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A C0B C3B) (t := W.st .A G0B []) (by decide) L R

theorem r_C_C2 (L R : ListBlank Bool) : Reaches (dR (C2B +> L) (C3B +> R)) (dR (F0B +> L) R) :=
  wreach_sound (n := 200) (s := W.st .A C2B C3B) (t := W.st .A F0B []) (by decide) L R

theorem r_P_end (L : ListBlank Bool) : Reaches (dR L (PB +> ∅)) (dL L (PB +> ∅)) := by
  refine wreach_cfg (n := 200) (s := W.st .A [] (PB ++ List.replicate 4 false))
    (t := W.exitL .C ([true, false] ++ (PB ++ List.replicate 2 false)))
    (by decide) L ∅ ?_ ?_
  · show dR L ((PB ++ List.replicate 4 false) +> ∅) = _
    rw [append_blanks]
  · rw [← append_blanks PB 2, dL_den']

theorem RulesAux.r_P_x (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ xB) +> R)) (dR (xB +> L) (PB +> R)) :=
  wreach_sound (n := 200) (s := W.st .A [] (PB ++ xB)) (t := W.st .A xB PB) (by decide) L R

theorem r_P_xn (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ bpow xB n) +> R)) (dR (bpow xB n +> L) (PB +> R)) := by
  induction n generalizing L with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : (PB ++ bpow xB (n + 1)) +> R = (PB ++ xB) +> bpow xB n +> R := by
      rw [bpow_succ, append_append, List.append_assoc]
    have h2 : bpow xB (n + 1) +> L = bpow xB n +> xB +> L := by rw [bpow_succ', append_append]
    rw [h1, h2]
    refine (r_P_x L _).trans ?_
    rw [append_append]
    exact ih _

theorem r_P_D_x (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ xB) +> R)) (dR ((DlB ++ C1B) +> L) (PB +> R)) :=
  wreach_sound (n := 400) (s := W.st .A [] (PB ++ DrB ++ xB)) (t := W.st .A (DlB ++ C1B) PB)
    (by decide) L R

theorem r_P_D_D (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ DrB ++ xB) +> R)) (dR ((DlB ++ C1B ++ C2B) +> L) R) :=
  wreach_sound (n := 400) (s := W.st .A [] (PB ++ DrB ++ DrB ++ xB))
    (t := W.st .A (DlB ++ C1B ++ C2B) []) (by decide) L R

theorem r_P_D_C (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ C3B ++ xB) +> R)) (dR ((DlB ++ G1B) +> L) (PB +> R)) :=
  wreach_sound (n := 400) (s := W.st .A [] (PB ++ DrB ++ C3B ++ xB))
    (t := W.st .A (DlB ++ G1B) PB) (by decide) L R

theorem r_P_D_P (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ PB) +> R)) (dR ((DlB ++ C1B) +> L) R) :=
  wreach_sound (n := 400) (s := W.st .A [] (PB ++ DrB ++ PB))
    (t := W.st .A (DlB ++ C1B) []) (by decide) L R

theorem RulesAux.r_P_D_seg (k : ℕ) (L R : ListBlank Bool) :
    Reaches (dR L (PB +> DrB +> bpow xB (k + 1) +> R))
      (dR (bpow xB k +> DlB +> C1B +> L) (PB +> R)) := by
  have e1 : PB +> DrB +> bpow xB (k + 1) +> R = (PB ++ DrB ++ xB) +> bpow xB k +> R := by
    rw [bpow_succ]; simp only [append_append, List.append_assoc]
  have e2 : DlB +> C1B +> L = (DlB ++ C1B) +> L := append_append _ _ _
  rw [e1, e2]
  refine (r_P_D_x L _).trans ?_
  rw [append_append]
  exact r_P_xn k _ _

theorem RulesAux.r_P_D_G1 (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ GrB) +> R)) (dR (HlB +> L) ((PB ++ DrB) +> R)) := by
  have e1 : (PB ++ DrB ++ GrB) +> R = PB +> DrB +> bpow xB 300 +> DrB +> bpow xB 30826 +> DrB +>
      bpow xB 72142 +> DrB +> bpow xB 3076 +> DrB +> bpow xB 1538 +> DrB +> R := by
    simp only [GrB, append_append, List.append_assoc]
  have e2 : HlB +> L = bpow xB 1537 +> DlB +> C1B +> bpow xB 3075 +> DlB +> C1B +>
      bpow xB 72141 +> DlB +> C1B +> bpow xB 30825 +> DlB +> C1B +> bpow xB 299 +> DlB +> C1B +> L := by
    simp only [HlB, append_append, List.append_assoc]
  have e3 : (PB ++ DrB) +> R = PB +> DrB +> R := (append_append _ _ _).symm
  rw [e1, e2, e3]
  exact (r_P_D_seg 299 _ _).trans <| (r_P_D_seg 30825 _ _).trans <| (r_P_D_seg 72141 _ _).trans <|
    (r_P_D_seg 3075 _ _).trans (r_P_D_seg 1537 _ _)

theorem r_P_D_G (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ DrB ++ bpow GrB n) +> R)) (dR (bpow HlB n +> L) ((PB ++ DrB) +> R)) := by
  induction n generalizing L with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : (PB ++ DrB ++ bpow GrB (n + 1)) +> R = (PB ++ DrB ++ GrB) +> bpow GrB n +> R := by
      rw [bpow_succ, append_append]; simp only [List.append_assoc]
    have h2 : bpow HlB (n + 1) +> L = bpow HlB n +> HlB +> L := by rw [bpow_succ', append_append]
    rw [h1, h2]
    refine (r_P_D_G1 L _).trans ?_
    rw [append_append (PB ++ DrB)]
    exact ih _

theorem r_P_C (L R : ListBlank Bool) :
    Reaches (dR L ((PB ++ C3B ++ xB) +> R)) (dL L ((PB ++ DrB ++ PB) +> R)) := by
  rw [dL_den']
  exact wreach_sound (n := 400) (s := W.st .A [] (PB ++ C3B ++ xB)) (by decide) L R

theorem r_P_P (L R : ListBlank Bool) : Reaches (dR L ((PB ++ PB) +> R)) (dR (xB +> L) R) :=
  wreach_sound (n := 400) (s := W.st .A [] (PB ++ PB)) (t := W.st .A xB []) (by decide) L R

theorem RulesAux.r_G1 (L R : ListBlank Bool) : Reaches (dR L (GrB +> R)) (dR (GlB +> L) R) := by
  have e1 : GrB +> R = bpow xB 300 +> DrB +> bpow xB 30826 +> DrB +> bpow xB 72142 +> DrB +>
      bpow xB 3076 +> DrB +> bpow xB 1538 +> DrB +> R := by
    simp only [GrB, append_append, List.append_assoc]
  have e2 : GlB +> L = DlB +> bpow xB 1538 +> DlB +> bpow xB 3076 +> DlB +> bpow xB 72142 +>
      DlB +> bpow xB 30826 +> DlB +> bpow xB 300 +> L := by
    simp only [GlB, append_append, List.append_assoc]
  rw [e1, e2]
  exact (r_xn 300 _ _).trans <| (r_D _ _).trans <| (r_xn 30826 _ _).trans <| (r_D _ _).trans <|
    (r_xn 72142 _ _).trans <| (r_D _ _).trans <| (r_xn 3076 _ _).trans <| (r_D _ _).trans <|
    (r_xn 1538 _ _).trans (r_D _ _)

theorem r_G (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dR L (bpow GrB n +> R)) (dR (bpow GlB n +> L) R) := by
  induction n generalizing L with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : bpow GrB (n + 1) +> R = GrB +> bpow GrB n +> R := by rw [bpow_succ, append_append]
    have h2 : bpow GlB (n + 1) +> L = bpow GlB n +> GlB +> L := by rw [bpow_succ', append_append]
    rw [h1, h2]
    exact (r_G1 L _).trans (ih _)

/-! ### Left-moving -/

theorem l_nil_C (R : ListBlank Bool) :
    Reaches (dL ∅ ((C3B ++ xB) +> R)) (dR ((DlB ++ C1B) +> ∅) (PB +> R)) := by
  refine wreach_cfg (n := 400) (s := W.st .C [false] ([false, true, false] ++ (C3B ++ xB)))
    (t := W.st .A (DlB ++ C1B) PB) (by decide) ∅ R ?_ rfl
  rw [← den_st_appR, ← dL_cons_eq_den,
    show (false :: [false]) = List.replicate 2 false from rfl, ← empty_eq_blanks]

theorem RulesAux.l_x (L R : ListBlank Bool) : Reaches (dL (xB +> L) R) (dL L (xB +> R)) := by
  rw [dL_den xB (by decide), dL_den']
  exact wreach_sound (n := 200) (by decide) L R

theorem l_xn (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dL (bpow xB n +> L) R) (dL L (bpow xB n +> R)) := by
  induction n generalizing R with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : bpow xB (n + 1) +> L = xB +> bpow xB n +> L := by rw [bpow_succ, append_append]
    have h2 : bpow xB (n + 1) +> R = bpow xB n +> xB +> R := by rw [bpow_succ', append_append]
    rw [h1, h2]
    exact (l_x _ R).trans (ih _)

theorem l_D (L R : ListBlank Bool) : Reaches (dL (DlB +> L) R) (dL L (DrB +> R)) := by
  rw [dL_den DlB (by decide), dL_den']
  exact wreach_sound (n := 200) (by decide) L R

theorem l_P (L R : ListBlank Bool) : Reaches (dL (PB +> L) R) (dL L (PB +> R)) := by
  rw [dL_den PB (by decide), dL_den']
  exact wreach_sound (n := 200) (by decide) L R

theorem l_C0 (L R : ListBlank Bool) : Reaches (dL (C0B +> L) R) (dR ((xB ++ C1B) +> L) R) := by
  rw [dL_den C0B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A (xB ++ C1B) []) (by decide) L R

theorem l_C1 (L R : ListBlank Bool) : Reaches (dL (C1B +> L) R) (dR (C2B +> L) R) := by
  rw [dL_den C1B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A C2B []) (by decide) L R

theorem l_C2 (L R : ListBlank Bool) : Reaches (dL (C2B +> L) R) (dR ((xB ++ C3B) +> L) R) := by
  rw [dL_den C2B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A (xB ++ C3B) []) (by decide) L R

theorem l_C3 (L R : ListBlank Bool) : Reaches (dL (C3B +> L) R) (dL L (C3B +> R)) := by
  rw [dL_den C3B (by decide), dL_den']
  exact wreach_sound (n := 200) (by decide) L R

theorem l_F0 (L R : ListBlank Bool) : Reaches (dL (F0B +> L) R) (dR ((xB ++ F1B) +> L) R) := by
  rw [dL_den F0B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A (xB ++ F1B) []) (by decide) L R

theorem l_F1 (L R : ListBlank Bool) : Reaches (dL (F1B +> L) R) (dR (F2B +> L) R) := by
  rw [dL_den F1B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A F2B []) (by decide) L R

theorem l_F2 (L R : ListBlank Bool) : Reaches (dL (F2B +> L) R) (dR ((xB ++ F3B) +> L) R) := by
  rw [dL_den F2B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A (xB ++ F3B) []) (by decide) L R

theorem l_F3 (L R : ListBlank Bool) :
    Reaches (dL ((F3B ++ xB) +> L) R) (dR ((DlB ++ C1B ++ PB) +> L) R) := by
  rw [dL_den (F3B ++ xB) (by decide)]
  exact wreach_sound (n := 400) (t := W.st .A (DlB ++ C1B ++ PB) []) (by decide) L R

theorem l_G0 (L R : ListBlank Bool) : Reaches (dL (G0B +> L) R) (dR ((xB ++ G1B) +> L) R) := by
  rw [dL_den G0B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A (xB ++ G1B) []) (by decide) L R

theorem l_G1 (L R : ListBlank Bool) : Reaches (dL (G1B +> L) R) (dR (G2B +> L) R) := by
  rw [dL_den G1B (by decide)]
  exact wreach_sound (n := 200) (t := W.st .A G2B []) (by decide) L R

theorem l_G2 (L R : ListBlank Bool) :
    Reaches (dL (G2B +> L) R) (dR ((xB ++ DlB ++ PB) +> L) R) := by
  rw [dL_den G2B (by decide)]
  exact wreach_sound (n := 400) (t := W.st .A (xB ++ DlB ++ PB) []) (by decide) L R

theorem RulesAux.l_Gs1 (L R : ListBlank Bool) : Reaches (dL (GlB +> L) R) (dL L (GrB +> R)) := by
  have e1 : GrB +> R = bpow xB 300 +> DrB +> bpow xB 30826 +> DrB +> bpow xB 72142 +> DrB +>
      bpow xB 3076 +> DrB +> bpow xB 1538 +> DrB +> R := by
    simp only [GrB, append_append, List.append_assoc]
  have e2 : GlB +> L = DlB +> bpow xB 1538 +> DlB +> bpow xB 3076 +> DlB +> bpow xB 72142 +>
      DlB +> bpow xB 30826 +> DlB +> bpow xB 300 +> L := by
    simp only [GlB, append_append, List.append_assoc]
  rw [e1, e2]
  exact (l_D _ _).trans <| (l_xn 1538 _ _).trans <| (l_D _ _).trans <| (l_xn 3076 _ _).trans <|
    (l_D _ _).trans <| (l_xn 72142 _ _).trans <| (l_D _ _).trans <| (l_xn 30826 _ _).trans <|
    (l_D _ _).trans (l_xn 300 _ _)

theorem l_Gs (n : ℕ) (L R : ListBlank Bool) :
    Reaches (dL (bpow GlB n +> L) R) (dL L (bpow GrB n +> R)) := by
  induction n generalizing R with
  | zero => exact Reaches.refl _
  | succ n ih =>
    have h1 : bpow GlB (n + 1) +> L = GlB +> bpow GlB n +> L := by rw [bpow_succ, append_append]
    have h2 : bpow GrB (n + 1) +> R = bpow GrB n +> GrB +> R := by rw [bpow_succ', append_append]
    rw [h1, h2]
    exact (l_Gs1 _ R).trans (ih _)

end Sk1.TM
