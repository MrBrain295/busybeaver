import Busybeaver.Deciders.Skelet.Skelet1Helpers
import Busybeaver.TM.Table.ClosedSet
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

/-!
# Skelet #1 — universe cycle and non-halting

This file continues the Lean port of `Coq-BB5/BusyCoq/Skelet1.v`.  It sits on top
of the accelerated `step` layer (`Skelet1Stride.lean`) and develops the
"universe cycle" self-similarity theorem `uni_cycle`, the `try_uni_cycle` /
`fullstep` wrappers, the `infinite_cycle` / `cycle_nonhalt` cyclic-family
argument, and finally the reflective reachability computation `doit` that
assembles `¬ M.halts init`.

Where the Coq development uses `positive`/`N` we use `ℕ`.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-! ## The distinguished blocks `F`, `G`, `J`, `K` and constants. -/

/-- Coq `F`. -/
def F : Ltape := [Lsym.xs 10344, Lsym.D, Lsym.xs 7640, Lsym.C2]

/-- Coq `G`. -/
def G : Rtape :=
  [Rsym.xs 300, Rsym.D, Rsym.xs 30826, Rsym.D, Rsym.xs 72142, Rsym.D,
   Rsym.xs 3076, Rsym.D, Rsym.xs 1538, Rsym.D]

/-- Coq `J`. -/
def J : Ltape :=
  [Lsym.D, Lsym.C2, Lsym.xs 95, Lsym.C0,
   Lsym.xs 7713, Lsym.D, Lsym.D, Lsym.xs 1866, Lsym.C1,
   Lsym.xs 13231, Lsym.D, Lsym.xs 6197, Lsym.C3,
   Lsym.xs 11066, Lsym.D, Lsym.xs 7279, Lsym.C0,
   Lsym.xs 10524, Lsym.D, Lsym.xs 7550, Lsym.C2,
   Lsym.xs 10389, Lsym.D, Lsym.xs 7618, Lsym.C1,
   Lsym.xs 10355, Lsym.D, Lsym.xs 7635, Lsym.C3,
   Lsym.xs 10347, Lsym.D, Lsym.xs 7639, Lsym.C3,
   Lsym.xs 10345, Lsym.D, Lsym.xs 7640, Lsym.C1]

/-- Coq `K`. -/
def K : Rtape :=
  [Rsym.xs 7639, Rsym.D, Rsym.xs 10347, Rsym.Cr,
   Rsym.xs 7635, Rsym.D, Rsym.xs 10355, Rsym.Cr,
   Rsym.xs 7619, Rsym.D, Rsym.xs 10387, Rsym.Cr,
   Rsym.xs 7555, Rsym.D, Rsym.xs 10515, Rsym.Cr,
   Rsym.xs 7299, Rsym.D, Rsym.xs 11027, Rsym.Cr,
   Rsym.xs 6275, Rsym.D, Rsym.xs 13075, Rsym.Cr,
   Rsym.xs 2179, Rsym.D, Rsym.D, Rsym.xs 7088, Rsym.Cr,
   Rsym.xs 1, Rsym.Cr, Rsym.xs 3849, Rsym.P]

/-- Coq `uni_P`. -/
def uni_P : ℕ := 53946

/-- Coq `uni_T = 4 * uni_P - 5`. -/
def uni_T : ℕ := 4 * uni_P - 5

/-! ## The universe-cycle theorem (Coq `uni_cycle`). -/

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

/-- Coq `uni_cycle`.  A single universe period: given a stride of length
`uni_T` on the right tape, the configuration advances by consuming `uni_P` from
the `l_xs` counter and appending one `F` on the left and one `G` on the right. --/

theorem uni_cycle (l : Ltape) (r r' : Rtape) (xs : ℕ)
    (h : stride 0 uni_T r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + (uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l, G ++ r') := by
  norm_num [uni_T, uni_P] at h ⊢
  repeat
    first
    | refine consume_stride_segment_cps
        (hreduce := by norm_num [strideK, rxs]) (h := by assumption) (hm := by omega) ?_
      intro u hu
    | refine (simple_step_spec _ _ (by rfl)).trans ?_
    | refine (stride_correct_0 _ _ _ (by assumption)).trans ?_
    | exact Machine.EvStep.refl

/-- `liftL` is congruent under a fixed prefix. -/
lemma liftL_append_congr (p a b : Ltape) (hab : liftL a = liftL b) :
    liftL (p ++ a) = liftL (p ++ b) := by
  induction p with
  | nil => simpa using hab
  | cons hd t ih => cases hd <;> simp only [List.cons_append, liftL, ih]

/-- `lpow b 1 = b`. -/
lemma lpow_one (b : List (Symbol 1)) : lpow b 1 = b := by
  simp [lpow]

/-- One `F` block equals `Fls 1` on the lift. -/
lemma liftL_Fls_one_eq (l : Ltape) : liftL (F ++ l) = liftL (Fls 1 l) := by
  rw [liftL_Fls, lpow_one, F]
  simp only [List.cons_append, List.nil_append, liftL]
  rw [Fl]
  simp only [List.append_assoc, ListBlank.append_assoc']

/-- One `G` block equals `Grs 1` on the lift. -/
lemma liftR_Grs_one_eq (r : Rtape) : liftR (G ++ r) = liftR (Grs 1 r) := by
  rw [liftR_Grs, lpow_one, G]
  simp only [List.cons_append, List.nil_append, liftR]
  rw [Gr]
  simp only [List.append_assoc, ListBlank.append_assoc']

/-- Coq `uni_cycle'`: the `uni_cycle` result phrased with the smart constructors
`Fls`/`Grs`. -/
theorem uni_cycle' (l : Ltape) (r r' : Rtape) (xs : ℕ)
    (h : stride 0 uni_T r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + (uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l, Grs 1 r') := by
  refine (uni_cycle l r r' xs h).trans ?_
  have hcfg :
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l, G ++ r')
        = lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l, Grs 1 r') := by
    simp only [lift]
    have hL : liftL (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l)
        = liftL (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l) := by
      have := liftL_append_congr (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J)
        (F ++ l) (Fls 1 l) (liftL_Fls_one_eq l)
      simpa [List.append_assoc] using this
    have hR : liftR (G ++ r') = liftR (Grs 1 r') := liftR_Grs_one_eq r'
    rw [hL, hR]
  rw [hcfg]
  exact Machine.EvStep.refl

/-
Coq `uni_cycles`: iterate `uni_cycle'` `n+1` times.
-/
/- Increase recursion depth for Lean tactics used in proofs. -/
theorem uni_cycles (n xs : ℕ) (l : Ltape) (r r' : Rtape)
    (h : stride 0 ((n + 1) * uni_T) r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + ((n + 1) * uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls (n + 1) l,
        Grs (n + 1) r') := by
  simp only [uni_T, uni_P] at h ⊢
    repeat'
    first
    | exact (simple_step_spec _ _ rfl).trans (by assumption)
    | apply consume_stride_segment_cps (h := h)
    · rfl
    · decide
    · clear h
     intro u h

/-! ## The `uni_cycle_count` bound. -/

/-- Coq `uni_cycle_count`. -/
def uni_cycle_count (xs : ℕ) (r : Rtape) : ℕ :=
  let xs_limit := (xs - 1) / uni_P
  if xs_limit = 0 then 0
  else
    match max_stride 0 r with
    | some strides => min xs_limit (strides / uni_T)
    | none => xs_limit

/-
Coq `uni_cycle_count_spec` (in `ℕ`, valid when the count is positive).
-/
lemma uni_cycle_count_spec (xs : ℕ) (r : Rtape) (h : 0 < uni_cycle_count xs r) :
    uni_cycle_count xs r * uni_P < xs := by
  grind +locals

/-! ## `strip_prefix` and `try_uni_cycle`. -/

/-- A decidable prefix-strip on lists (Coq `strip_prefix'` with `eqb_l`). -/
def stripPrefix {α : Type*} [DecidableEq α] : List α → List α → Option (List α)
  | [], ys => some ys
  | _ :: _, [] => none
  | xh :: xt, yh :: yt => if xh = yh then stripPrefix xt yt else none

lemma stripPrefix_spec {α : Type*} [DecidableEq α] (xs ys zs : List α)
    (h : stripPrefix xs ys = some zs) : ys = xs ++ zs := by
  induction' xs with x xs ih generalizing ys zs;
  · cases ys <;> cases h <;> rfl;
  · rcases ys with ( _ | ⟨ y, ys ⟩ ) <;> simp_all +decide [ stripPrefix ];
    exact ih _ _ h.2

/-- Coq `try_uni_cycle`. -/
def try_uni_cycle : conf → Option conf
  | (.right, Lsym.D :: Lsym.C1 :: Lsym.xs xs :: l, r) =>
    match stripPrefix J l with
    | some l =>
      match uni_cycle_count xs r with
      | 0 => none
      | n + 1 =>
        match stride 0 ((n + 1) * uni_T) r with
        | some r' =>
          some (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs - (n + 1) * uni_P) ::
            J ++ Fls (n + 1) l, Grs (n + 1) r')
        | none => none
    | none => none
  | _ => none

lemma try_uni_cycle_spec (c c' : conf) (h : try_uni_cycle c = some c') :
    lift c -[M]->* lift c' := by
  obtain ⟨l0, r⟩ : ∃ l0 r, c = (.right, l0, r) := by
    rcases c with ⟨ _ | _, _ | _, _ | _ ⟩ <;> tauto;
  rcases r with ⟨ r, rfl ⟩;
  obtain ⟨l, xs, hl⟩ : ∃ l xs, l0 = Lsym.D :: Lsym.C1 :: Lsym.xs xs :: l := by
    rcases l0 with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | l0 ⟩ ⟩ ⟩ ) <;> simp_all +decide [ try_uni_cycle ]; all_goals cases a <;> cases b <;> cases c <;> tauto;
  obtain ⟨l', hl'⟩ : ∃ l', stripPrefix J l = some l' := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨n, hn⟩ : ∃ n, uni_cycle_count xs r = n + 1 := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨r', hr'⟩ : ∃ r', stride 0 ((n + 1) * uni_T) r = some r' := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨c'', hc''⟩ : c' = (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs - (n + 1) * uni_P) :: J ++ Fls (n + 1) l', Grs (n + 1) r') := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨u, hu⟩ : ∃ u, xs = u + ((n + 1) * uni_P + 1) := by
    have := uni_cycle_count_spec xs r ( by linarith );
    exact ⟨ xs - ( ( n + 1 ) * uni_P + 1 ), by rw [ Nat.sub_add_cancel ( by nlinarith ) ] ⟩;
  convert uni_cycles n u l' r r' hr' using 1;
  · have := stripPrefix_spec J l l' hl'; aesop;
  · simp +decide [hu];
    simp +decide [Nat.add_sub_assoc]

/-- Coq `fullstep`. -/
def fullstep (c : conf) : Option conf :=
  match try_uni_cycle c with
  | some c' => some c'
  | none => step c

lemma fullstep_spec (c c' : conf) (h : fullstep c = some c') :
    lift c -[M]->* lift c' := by
  unfold fullstep at h;
  grind +suggestions

/-! ## Iterating `fullstep`. -/

/-- Coq `steps`. -/
def steps : ℕ → conf → Option conf
  | 0, c => some c
  | n + 1, c =>
    match fullstep c with
    | some c' => steps n c'
    | none => none

lemma steps_spec (n : ℕ) (c c' : conf) (h : steps n c = some c') :
    lift c -[M]->* lift c' := by
  induction' n with n ih generalizing c;
  · cases h ; tauto;
  · cases h' : fullstep c <;> simp_all +decide [ steps ];
    exact fullstep_spec _ _ h' |> fun h'' => h''.trans ( ih _ _ _ h )

/-! ## The infinite cyclic family. -/

/-- An `EvStep` between distinct configurations is a `Progress` (≥ 1 step). -/
lemma evstep_progress_of_ne {A B : Config 4 1} (h : A -[M]->* B) (hne : A ≠ B) :
    A -[M]->+ B := by
  cases h with
  | refl => exact absurd rfl hne
  | step hstep tail => exact Trans.trans (Machine.Progress.single hstep) tail

/-- `steps` splits additively. -/
lemma steps_add (m n : ℕ) (c : conf) :
    steps (m + n) c = (steps m c).bind (steps n) := by
  induction m generalizing c with
  | zero => simp [steps]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    cases hf : fullstep c with
    | none => simp [steps, hf]
    | some c' => simp only [steps, hf]; exact ih c'

/-- A right-facing lift is never equal to a left-facing lift (states differ). -/
lemma lift_right_ne_left (a b : Ltape) (c d : Rtape) :
    lift (.right, a, c) ≠ lift (.left, b, d) := by
  intro h
  have hs := congrArg Config.state h
  simp only [lift, AR, CL, headL] at hs
  exact absurd hs (by decide)

/-- The configuration reached after 30 accelerated steps from the reset
configuration (with symbolic tail `l`).  It faces `left`. -/
def cyc30 (l : Ltape) : conf :=
  (.left,
    [Lsym.C0, Lsym.xs 7087, Lsym.D, Lsym.D, Lsym.xs 2179, Lsym.C0,
     Lsym.xs 13074, Lsym.D, Lsym.xs 6275, Lsym.C0, Lsym.xs 11026, Lsym.D,
     Lsym.xs 7299, Lsym.C0, Lsym.xs 10514, Lsym.D, Lsym.xs 7555, Lsym.C0,
     Lsym.xs 10386, Lsym.D, Lsym.xs 7619, Lsym.C0, Lsym.xs 10354, Lsym.D,
     Lsym.xs 7635, Lsym.C0, Lsym.xs 10346, Lsym.D, Lsym.xs 7639, Lsym.C0] ++ l,
    [Rsym.Cr, Rsym.xs 3851, Rsym.P])

set_option maxRecDepth 200000 in
/-- Coq `infinite_cycle`: the reset configuration `(right, l_C0 :: l, K)` returns
to a larger copy of itself (`F` prepended), making genuine progress. -/
lemma infinite_cycle (l : Ltape) :
    lift (.right, Lsym.C0 :: l, K) -[M]->+ lift (.right, Lsym.C0 :: F ++ l, K) := by
  have h30 : steps 30 (.right, Lsym.C0 :: l, K) = some (cyc30 l) := by
    rw [cyc30]; rfl
  have h982 : steps 982 (.right, Lsym.C0 :: l, K) = some (.right, Lsym.C0 :: F ++ l, K) := by
    rfl
  have h952 : steps 952 (cyc30 l) = some (.right, Lsym.C0 :: F ++ l, K) := by
    have := steps_add 30 952 (.right, Lsym.C0 :: l, K)
    rw [h30] at this
    simpa [h982] using this.symm
  have e1 : lift (.right, Lsym.C0 :: l, K) -[M]->* lift (cyc30 l) :=
    steps_spec 30 _ _ h30
  have e2 : lift (cyc30 l) -[M]->* lift (.right, Lsym.C0 :: F ++ l, K) :=
    steps_spec 952 _ _ h952
  have hne : lift (.right, Lsym.C0 :: l, K) ≠ lift (cyc30 l) := by
    rw [cyc30]; exact lift_right_ne_left _ _ _ _
  exact Trans.trans (evstep_progress_of_ne e1 hne) e2

/-- Coq `cycle_nonhalt`: any reset configuration does not halt. -/
lemma cycle_nonhalt (l : Ltape) : ¬ M.halts (lift (.right, Lsym.C0 :: l, K)) := by
  have cs : ClosedSet M (fun C => ∃ l, C = lift (.right, Lsym.C0 :: l, K))
      (lift (.right, Lsym.C0 :: l, K)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, l', rfl⟩
      exact ⟨⟨lift (.right, Lsym.C0 :: F ++ l', K), F ++ l', rfl⟩, infinite_cycle l'⟩
    · exact ⟨⟨_, l, rfl⟩, Machine.EvStep.refl⟩
  exact cs.nonHalting

/-! ## The reflective reachability computation. -/

/-- Coq `is_cycling`. -/
def is_cycling : conf → Bool
  | (.right, Lsym.C0 :: _, r) => decide (r = K)
  | _ => false

lemma is_cycling_spec (c : conf) (h : is_cycling c = true) :
    ¬ M.halts (lift c) := by
  rcases c with ⟨ d, l, r ⟩;
  rcases d with ( _ | _ | d ) <;> rcases l with ( _ | _ | l ) <;> simp_all +decide [ is_cycling ];
  exact cycle_nonhalt _

/-- Coq `doit`. -/
def doit : ℕ → conf → Bool
  | 0, _ => false
  | n + 1, c =>
    if is_cycling c then true
    else
      match fullstep c with
      | some c' => doit n c'
      | none => false

/-
If `A -[M]->* B` and `B` does not halt, then `A` does not halt.
-/
lemma multistep_nonhalt {A B : Config 4 1} (h : A -[M]->* B) (hB : ¬ M.halts B) :
    ¬ M.halts A := by
  convert Machine.halts.skip_evstep h ‹_› using 1

lemma doit_spec (n : ℕ) (c : conf) (h : doit n c = true) :
    ¬ M.halts (lift c) := by
  induction' n with n ih generalizing c;
  · cases h;
  · by_cases h_cycling : is_cycling c;
    · exact is_cycling_spec c h_cycling;
    · obtain ⟨c', hc'⟩ : ∃ c', fullstep c = some c' ∧ doit n c' = true := by
        unfold doit at h; aesop;
      exact multistep_nonhalt ( fullstep_spec c c' hc'.1 ) ( ih c' hc'.2 )

/-- The reflective 88-million-step run. -/
lemma doit_result : doit 88000000 initial = true := by
  native_decide

/-- Skelet #1 does not halt from the blank tape. -/
theorem nonHalting : ¬ M.halts init := by
  refine multistep_nonhalt init_reach ?_
  exact doit_spec 88000000 initial doit_result

end Deciders.Skelet.Skelet1
