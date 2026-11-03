import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Defs
import Mathlib.Tactic

/-!
# Correctness of the deferred (lazy) tick

The main result, `Sk1.RT.tick_den`, states that one lazy tick (`O(1)` work)
denotes exactly one eager sweep (`sweep 0 1`, linear in the right tape).
-/

namespace Sk1

/-! ## Basic facts about the eager sweep -/

theorem pushX_zero (t : List RI) : pushX 0 t = t := by simp [pushX]

theorem sweep_pushX (a b n : Nat) (L : List RI) :
    sweep a n (pushX b L) = sweep (a + b) n L := by
  unfold pushX
  by_cases hb : b = 0
  · subst hb; simp
  · simp only [hb, ite_false]
    match L with
    | [] => simp [sweep]
    | .x m :: t => simp [sweep, Nat.add_assoc]
    | .D :: t => simp [sweep]
    | .C :: t => simp [sweep]
    | .P :: t => simp [sweep]
    | .G g :: t => simp [sweep]

theorem pushX_pushX (k m : Nat) (L : List RI) : pushX k (pushX m L) = pushX (k + m) L := by
  unfold pushX
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hk : k = 0
  · subst hk; simp [hm]
  rcases L with _ | ⟨i, t⟩
  · simp [hm, hk]
  · cases i <;> simp [hm, hk, Nat.add_assoc]

theorem pushG_pushG (g m : Nat) (L : List RI) : pushG g (pushG m L) = pushG (g + m) L := by
  unfold pushG
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hg : g = 0
  · subst hg; simp [hm]
  rcases L with _ | ⟨i, t⟩
  · simp [hm, hg]
  · cases i <;> simp [hm, hg, Nat.add_assoc]

theorem sweep_pushG (a g n : Nat) (hg : g ≠ 0) (L : List RI) :
    sweep a n (pushG g L) = (sweep 0 n L).map (fun t => pushX a (pushG g t)) := by
  match L with
  | .G m :: t =>
    have : pushG g (.G m :: t) = .G (g + m) :: t := by simp [pushG, hg]
    rw [this]
    simp only [sweep, Option.map_map, Function.comp_def, pushX_zero, pushG_pushG]
  | [] => simp [pushG, hg, sweep]
  | .x m :: t => simp [pushG, hg, sweep]
  | .D :: t => simp [pushG, hg, sweep]
  | .C :: t => simp [pushG, hg, sweep]
  | .P :: t => simp [pushG, hg, sweep]

theorem sweep_D (a n : Nat) (L : List RI) :
    sweep a n (.D :: L) = (sweep 0 n L).map (fun t => pushX a (.D :: t)) := by
  simp [sweep]

theorem sweep_P (a n : Nat) (L : List RI) (h : L ≠ []) : sweep a n (.P :: L) = none := by
  rcases L with _ | ⟨i, t⟩
  · exact absurd rfl h
  · simp [sweep]

theorem sweep_C (a n : Nat) (L : List RI) :
    sweep a n (.C :: L) =
      if n ≤ a then (sweep 0 (4 * n) L).map fun t => pushX (a - n) (.C :: pushX (2 * n) t)
      else none := by
  simp [sweep]

theorem sweep_Pend (a n : Nat) : sweep a n [.P] = some (pushX a [.P]) := by
  simp [sweep]

/-! ## Sweeping across a level -/

/-- No `G 0` separators (they would silently merge runs). -/
def Seg.NZ (g : Seg) : Prop := ∀ p ∈ g.segs, p.2 ≠ .G 0

theorem sep_sweep_push (a n : Nat) (sp : Sep) (hP : sp ≠ .P) (hG : sp ≠ .G 0) (L : List RI) :
    sweep a n (sp.push L) = (sweep 0 n L).map (fun t => pushX a (sp.push t)) := by
  cases sp with
  | D => exact sweep_D a n L
  | G k => exact sweep_pushG a k n (fun h => hG (by rw [h])) L
  | P => exact absurd rfl hP

theorem seg_items_nil (tr : Nat) (T : List RI) : Seg.items ⟨[], tr⟩ T = pushX tr T := rfl

theorem seg_items_cons (b : Nat) (sp : Sep) (rest : List (Nat × Sep)) (tr : Nat) (T : List RI) :
    Seg.items ⟨(b, sp) :: rest, tr⟩ T = pushX b (sp.push (Seg.items ⟨rest, tr⟩ T)) := rfl

theorem seg_items_trail (segs : List (Nat × Sep)) (k : Nat) (T : List RI) :
    Seg.items ⟨segs, 0⟩ (pushX k T) = Seg.items ⟨segs, k⟩ T := by
  simp [Seg.items, pushX_zero]

theorem pushX_ne_nil (n : Nat) (T : List RI) (h : T ≠ []) : pushX n T ≠ [] := by
  unfold pushX; by_cases hn : n = 0 <;> simp [hn, h]; split <;> simp

theorem sep_push_ne_nil (sp : Sep) (T : List RI) (h : T ≠ []) : sp.push T ≠ [] := by
  cases sp <;> simp [Sep.push, pushG]
  rename_i k; by_cases hk : k = 0 <;> simp [hk, h]; split <;> simp

theorem seg_hasP_cons (b : Nat) (sp : Sep) (rest : List (Nat × Sep)) (tr : Nat) :
    Seg.hasP ⟨(b, sp) :: rest, tr⟩ = ((sp == .P) || Seg.hasP ⟨rest, tr⟩) := by
  simp [Seg.hasP, List.any_cons]

theorem seg_items_ne_nil (g : Seg) (T : List RI) (h : T ≠ []) : g.items T ≠ [] := by
  obtain ⟨segs, tr⟩ := g
  induction segs with
  | nil => exact pushX_ne_nil _ _ h
  | cons p rest ih =>
    obtain ⟨b, sp⟩ := p
    rw [seg_items_cons]; exact pushX_ne_nil _ _ (sep_push_ne_nil _ _ ih)

/-- Sweeping across a level: the middle of the level is unchanged. -/
theorem seg_sweep_items (g : Seg) (hP : g.hasP = false) (hz : g.NZ) (a n : Nat) (T : List RI) :
    sweep a n (g.items T) =
      if g.segs = [] then sweep (a + g.trail) n T
      else (sweep g.trail n T).map (fun t => (Seg.pushX a ⟨g.segs, 0⟩).items t) := by
  obtain ⟨segs, tr⟩ := g
  induction segs generalizing a with
  | nil => simp [seg_items_nil, sweep_pushX]
  | cons p rest ih =>
    obtain ⟨b, sp⟩ := p
    have hsp : sp ≠ .P := by
      intro h; subst h; simp [Seg.hasP] at hP
    have hG : sp ≠ .G 0 := hz _ (List.mem_cons_self ..)
    have hP' : (Seg.hasP ⟨rest, tr⟩) = false := by
      rw [seg_hasP_cons] at hP; cases sp <;> simp_all
    have hz' : Seg.NZ ⟨rest, tr⟩ := fun q hq => hz q (List.mem_cons_of_mem _ hq)
    rw [seg_items_cons, sweep_pushX, sep_sweep_push _ _ _ hsp hG, ih 0 hP' hz']
    simp only [List.cons_ne_nil, ite_false]
    have key : ∀ t, (Seg.pushX a ⟨(b, sp) :: rest, 0⟩).items t
        = pushX (a + b) (sp.push ((Seg.pushX 0 ⟨rest, 0⟩).items t)) := by
      intro t
      by_cases ha : a = 0
      · subst ha; simp [Seg.pushX, seg_items_cons]
      · simp [Seg.pushX, ha, seg_items_cons, Nat.add_comm]
    simp only [key]
    by_cases hr : rest = []
    · subst hr
      simp [seg_items_nil, Seg.pushX, pushX_zero]
    · simp [hr]; rfl

theorem seg_sweep_items_hasP (g : Seg) (hP : g.hasP = true) (a n : Nat) (T : List RI)
    (hT : T ≠ []) : sweep a n (g.items T) = none := by
  obtain ⟨segs, tr⟩ := g
  induction segs generalizing a with
  | nil => simp [Seg.hasP] at hP
  | cons p rest ih =>
    obtain ⟨b, sp⟩ := p
    rw [seg_items_cons, sweep_pushX]
    have hne : Seg.items ⟨rest, tr⟩ T ≠ [] := seg_items_ne_nil _ _ hT
    by_cases hsp : sp = .P
    · subst hsp; exact sweep_P _ _ _ hne
    have hP' : (Seg.hasP ⟨rest, tr⟩) = true := by
      rw [seg_hasP_cons] at hP
      cases h : Seg.hasP ⟨rest, tr⟩
      · rw [h] at hP; cases sp <;> simp_all
      · rfl
    by_cases hG : sp = .G 0
    · subst hG; simp only [Sep.push, pushG, ite_true]; exact ih _ hP'
    · rw [sep_sweep_push _ _ _ hsp hG, ih 0 hP']; rfl

theorem seg_items_pushX (g : Seg) (k : Nat) (T : List RI) :
    pushX k (g.items T) = (g.pushX k).items T := by
  obtain ⟨segs, tr⟩ := g
  by_cases hk : k = 0
  · subst hk; simp [Seg.pushX, pushX_zero]
  rcases segs with _ | ⟨⟨b, sp⟩, rest⟩
  · simp [Seg.pushX, hk, seg_items_nil, pushX_pushX, Nat.add_comm]
  · simp [Seg.pushX, hk, seg_items_cons, pushX_pushX, Nat.add_comm]

/-- Sweep with multiplier `m` across a non-final level. -/
theorem seg_sweep_items_C (g : Seg) (hP : g.hasP = false) (hz : g.NZ) (m : Nat) (X : List RI) :
    sweep 0 m (g.items (.C :: X)) =
      if m ≤ g.trail then
        (sweep 0 (4 * m) X).map fun t => (⟨g.segs, g.trail - m⟩ : Seg).items (.C :: pushX (2 * m) t)
      else none := by
  rw [seg_sweep_items g hP hz, sweep_C]
  obtain ⟨segs, tr⟩ := g
  by_cases hs : segs = []
  · subst hs; simp; rfl
  · simp only [hs, ite_false, sweep_C]
    by_cases hm : m ≤ tr
    · simp [hm, Option.map_map, Function.comp_def, Seg.pushX, seg_items_trail]
    · simp [hm]

/-- Sweep across the final level. -/
theorem seg_sweep_items_P (g : Seg) (hP : g.hasP = false) (hz : g.NZ) (m : Nat) :
    sweep 0 m (g.items [.P]) = some (g.items [.P]) := by
  rw [seg_sweep_items g hP hz, sweep_Pend]
  obtain ⟨segs, tr⟩ := g
  by_cases hs : segs = []
  · subst hs; simp; rfl
  · simp [hs, Seg.pushX, seg_items_trail, sweep_Pend]

/-! ## Pending summaries -/

theorem seg_apply_hasP (s r : Nat) (last termP : Bool) (g g' : Seg)
    (h : g.apply s r last termP = some g') : g'.hasP = g.hasP := by
  obtain ⟨segs, tr⟩ := g
  unfold Seg.apply at h
  split_ifs at h <;> (try cases h) <;> (try rfl)
  all_goals
    rcases segs with _ | ⟨⟨a, sp⟩, rest⟩ <;> simp at h <;>
      (try cases h) <;> simp_all [Seg.hasP]

theorem seg_apply_NZ (s r : Nat) (last termP : Bool) (g g' : Seg) (hz : g.NZ)
    (h : g.apply s r last termP = some g') : g'.NZ := by
  obtain ⟨segs, tr⟩ := g
  unfold Seg.apply at h
  split_ifs at h <;> (try cases h) <;> (try exact hz)
  all_goals
    rcases segs with _ | ⟨⟨a, sp⟩, rest⟩ <;> simp at h <;>
      (try cases h) <;> simp_all [Seg.NZ] <;> exact hz.2

/-- Applying a composed summary is applying the summaries one after the other. -/
theorem seg_apply_comp (S R n : Nat) (last : Bool) (g : Seg) (h1 : S ≤ R) (h2 : S = 0 → R = 0)
    (hn : 0 < n) :
    g.apply (S + 2 * n) (max R (S + 4 * n)) last true =
      (g.apply S R last true).bind (Seg.apply (2 * n) (4 * n) last true) := by
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS; have := h2 rfl; subst this; simp [Seg.apply]
  have hS' : S ≠ 0 := by omega
  have hn' : n ≠ 0 := by omega
  obtain ⟨segs, tr⟩ := g
  by_cases hP : Seg.hasP ⟨segs, tr⟩ = true
  · simp [Seg.apply, hP, hS']
  simp only [Bool.not_eq_true] at hP
  rcases segs with _ | ⟨⟨a, sp⟩, rest⟩ <;> cases last
  · simp only [Seg.apply, hP, hS']
    simp
    split_ifs <;> simp_all [Seg.apply, Seg.hasP] <;> omega
  · simp [Seg.apply, Seg.hasP, hS', hn']; omega
  · have e : ∀ x t', Seg.hasP ⟨(x, sp) :: rest, t'⟩ = false := fun x t' => by
      simpa [Seg.hasP] using hP
    simp only [Seg.apply, hP, hS']
    simp
    split_ifs <;> simp [Seg.apply, e, hn'] <;> omega
  · simp [Seg.apply, hP, seg_hasP_cons, hS', hn']
    simp_all [seg_hasP_cons]; omega

theorem seg_apply_tick_mid (n : Nat) (g : Seg) (hn : 0 < n) :
    g.apply (2 * n) (4 * n) false true =
      if g.hasP then none
      else if 4 * n ≤ g.trail then some (Seg.pushX (2 * n) ⟨g.segs, g.trail - 4 * n⟩)
      else none := by
  have hn' : 2 * n ≠ 0 := by omega
  obtain ⟨segs, tr⟩ := g
  by_cases hP : Seg.hasP ⟨segs, tr⟩ = true
  · simp [Seg.apply, hP, hn']
  simp only [Bool.not_eq_true] at hP
  rcases segs with _ | ⟨⟨a, sp⟩, rest⟩
  · simp [Seg.apply, hP, hn', Seg.pushX]
    split_ifs <;> (try simp) <;> omega
  · simp [Seg.apply, hP, hn', Seg.pushX]
    split_ifs <;> (try simp) <;> omega

theorem seg_apply_tick_last (n : Nat) (g : Seg) (hn : 0 < n) :
    g.apply (2 * n) (4 * n) true true =
      if g.hasP then none else some (g.pushX (2 * n)) := by
  have hn' : 2 * n ≠ 0 := by omega
  obtain ⟨segs, tr⟩ := g
  by_cases hP : Seg.hasP ⟨segs, tr⟩ = true
  · simp [Seg.apply, hP, hn']
  simp only [Bool.not_eq_true] at hP
  rcases segs with _ | ⟨⟨a, sp⟩, rest⟩ <;> simp [Seg.apply, hP, hn', Seg.pushX]

/-! ## The deferred levels -/

/-- Invariant of a deferred level. -/
def LBlk.Inv (b : LBlk) : Prop := b.body.NZ ∧ b.s ≤ b.r ∧ (b.s = 0 → b.r = 0)

theorem matBelow_cons (tp : Bool) (s r : Nat) (b : LBlk) (bs : List LBlk) :
    matBelow tp s r (b :: bs) =
      (b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty tp).bind
        (fun g => (matBelow tp (4 * (b.s + s)) (4 * max b.r (b.s + r)) bs).map (g :: ·)) := by
  simp only [matBelow, comp]
  cases b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty tp <;> rfl

theorem matBelow_cons_ne (s r : Nat) (b : LBlk) (bs : List LBlk) :
    matBelow true s r (b :: bs) ≠ some [] := by
  simp only [matBelow]
  split <;> simp

/-- One more tick (multiplier `n`) arriving at the first deferred level. -/
theorem matBelow_tick (bs : List LBlk) (hinv : ∀ b ∈ bs, b.Inv) (s r n : Nat) (h1 : s ≤ r)
    (h2 : s = 0 → r = 0) (hn : 0 < n) (g : Seg) (gs : List Seg)
    (h : matBelow true s r bs = some (g :: gs)) :
    (matBelow true (s + 2 * n) (max r (s + 4 * n)) bs).map (flatBelow true) =
      (sweep 0 (4 * n) (g.items (flatBelow true gs))).map fun t => .C :: pushX (2 * n) t := by
  induction bs generalizing s r n g gs with
  | nil => simp [matBelow] at h
  | cons b bs ih =>
    obtain ⟨hz, hb1, hb2⟩ := hinv b (List.mem_cons_self ..)
    have hinv' : ∀ b ∈ bs, b.Inv := fun b hb => hinv b (List.mem_cons_of_mem _ hb)
    rw [matBelow_cons] at h ⊢
    have e1 : b.s + (s + 2 * n) = (b.s + s) + 2 * n := by omega
    have e2 : max b.r (b.s + max r (s + 4 * n)) = max (max b.r (b.s + r)) ((b.s + s) + 4 * n) := by
      omega
    rw [e1, e2]
    set S := b.s + s with hS
    set R := max b.r (b.s + r) with hR
    have hSR : S ≤ R := by omega
    have hSR2 : S = 0 → R = 0 := by omega
    rw [seg_apply_comp S R n _ _ hSR hSR2 hn]
    cases hg0 : b.body.apply S R bs.isEmpty true with
    | none => simp [hg0] at h
    | some g0 =>
      simp only [hg0, Option.bind_some, Option.map_eq_some_iff, List.cons.injEq] at h
      obtain ⟨gs', hgs', rfl, rfl⟩ := h
      have hzg : g0.NZ := seg_apply_NZ _ _ _ _ _ _ hz hg0
      simp only [Option.bind_some]
      rcases bs with _ | ⟨b2, bs2⟩
      · simp only [matBelow] at hgs'
        cases hgs'
        simp only [List.isEmpty_nil]
        rw [seg_apply_tick_last n g0 hn]
        by_cases hP : g0.hasP = true
        · simp [hP, seg_sweep_items_hasP g0 hP 0 (4 * n) (flatBelow true []) (by simp [flatBelow])]
        · simp only [Bool.not_eq_true] at hP
          simp [hP, seg_sweep_items_P g0 hP hzg, flatBelow, matBelow, seg_items_pushX]
      · obtain ⟨g2, gs2, rfl⟩ : ∃ g2 gs2, gs' = g2 :: gs2 := by
          rcases gs' with _ | ⟨g2, gs2⟩
          · exact absurd hgs' (matBelow_cons_ne _ _ _ _)
          · exact ⟨g2, gs2, rfl⟩
        simp only [List.isEmpty_cons]
        rw [seg_apply_tick_mid n g0 hn]
        by_cases hP : g0.hasP = true
        · simp [hP, seg_sweep_items_hasP g0 hP 0 (4 * n) (flatBelow true (g2 :: gs2))
            (by simp [flatBelow])]
        simp only [Bool.not_eq_true] at hP
        simp only [flatBelow, hP, Bool.false_eq_true, ite_false]
        rw [seg_sweep_items_C g0 hP hzg]
        by_cases hm : 4 * n ≤ g0.trail
        · simp only [hm, ite_true, Option.bind_some, Option.map_map]
          have e3 : 4 * (S + 2 * n) = 4 * S + 2 * (4 * n) := by ring
          have e4 : 4 * max R (S + 4 * n) = max (4 * R) (4 * S + 4 * (4 * n)) := by omega
          rw [e3, e4]
          have hih := ih hinv' (4 * S) (4 * R) (4 * n) (by omega) (by omega) (by omega) g2 gs2 hgs'
          have hf : (flatBelow true ∘ fun x =>
              Seg.pushX (2 * n) { segs := g0.segs, trail := g0.trail - 4 * n } :: x) =
              (fun x => RI.C :: (Seg.pushX (2 * n)
                { segs := g0.segs, trail := g0.trail - 4 * n }).items x) ∘ flatBelow true := by
            funext x; rfl
          rw [hf, ← Option.map_map, hih, Option.map_map]
          congr 1
          funext t
          simp [seg_items_pushX]
        · simp [hm]

/-! ## The main theorem -/

/-- Invariant of a lazy tape. -/
def RT.Inv (t : RT) : Prop := t.top.NZ ∧ ∀ b ∈ t.below, b.Inv

/-- **Correctness of the lazy tick.**  A lazy tick (constant work) denotes exactly one
eager sweep of the right tape. -/
theorem RT.tick_den (t t' : RT) (hinv : t.Inv) (L : List RI) (hL : t.den = some L)
    (ht : t.tick = some t') : t'.den = sweep 0 1 L := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hzt, hinvb⟩ := hinv
  simp only at hzt hinvb
  cases termP
  · simp [RT.tick] at ht
  by_cases hP : top.hasP = true
  · simp [RT.tick, hP] at ht
  simp only [Bool.not_eq_true] at hP
  rcases below with _ | ⟨b, bs⟩
  · simp [RT.tick, hP] at ht
    subst ht
    simp [RT.den, matBelow] at hL
    subst hL
    simp [RT.den, matBelow, flatBelow, seg_sweep_items_P top hP hzt]
  · by_cases h1 : 1 ≤ top.trail
    · simp [RT.tick, hP, h1] at ht
      subst ht
      simp only [RT.den, Option.map_eq_some_iff] at hL
      obtain ⟨gs, hgs, rfl⟩ := hL
      obtain ⟨g, gs', rfl⟩ : ∃ g gs', gs = g :: gs' := by
        rcases gs with _ | ⟨g, gs'⟩
        · exact absurd hgs (matBelow_cons_ne _ _ _ _)
        · exact ⟨g, gs', rfl⟩
      have hm : matBelow true 0 0 (⟨b.body, b.s + 2, max b.r (b.s + 4)⟩ :: bs) =
          matBelow true (0 + 2 * 1) (max 0 (0 + 4 * 1)) (b :: bs) := by
        rw [matBelow_cons, matBelow_cons]
        simp only
        have e1 : b.s + 2 + 0 = b.s + (0 + 2 * 1) := by omega
        have e2 : max (max b.r (b.s + 4)) (b.s + 2 + 0) = max b.r (b.s + max 0 (0 + 4 * 1)) := by
          omega
        rw [e1, e2]
      have key := matBelow_tick (b :: bs) hinvb 0 0 1 le_rfl (fun _ => rfl) one_pos g gs' hgs
      simp only [RT.den]
      rw [hm]
      have hf : (fun gs => (⟨top.segs, top.trail - 1⟩ : Seg).items (flatBelow true gs)) =
          (fun x => (⟨top.segs, top.trail - 1⟩ : Seg).items x) ∘ flatBelow true := rfl
      rw [hf, ← Option.map_map, key, Option.map_map]
      simp only [flatBelow]
      rw [seg_sweep_items_C top hP hzt 1]
      simp [h1, Function.comp_def]
    · simp [RT.tick, hP, h1] at ht

theorem RT.tickN_den (t t' : RT) (m : Nat) (hm : 0 < m) (hinv : t.Inv)
    (L : List RI) (hL : t.den = some L) (ht : RT.tickN m t = some t') :
    t'.den = sweep 0 m L := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hzt, hinvb⟩ := hinv
  simp only at hzt hinvb
  cases termP
  · simp [RT.tickN] at ht
  by_cases hP : top.hasP = true
  · simp [RT.tickN, hP] at ht
  simp only [Bool.not_eq_true] at hP
  rcases below with _ | ⟨b, bs⟩
  · simp [RT.tickN, hP] at ht
    subst ht
    simp [RT.den, matBelow] at hL
    subst hL
    simp [RT.den, matBelow, flatBelow, seg_sweep_items_P top hP hzt]
  · by_cases h1 : m ≤ top.trail
    · simp [RT.tickN, hP, h1] at ht
      subst ht
      simp only [RT.den, Option.map_eq_some_iff] at hL
      obtain ⟨gs, hgs, rfl⟩ := hL
      obtain ⟨g, gs', rfl⟩ : ∃ g gs', gs = g :: gs' := by
        rcases gs with _ | ⟨g, gs'⟩
        · exact absurd hgs (matBelow_cons_ne _ _ _ _)
        · exact ⟨g, gs', rfl⟩
      have hmBelow :
          matBelow true 0 0
            (⟨b.body, b.s + 2 * m, max b.r (b.s + 4 * m)⟩ :: bs) =
          matBelow true (0 + 2 * m) (max 0 (0 + 4 * m)) (b :: bs) := by
        rw [matBelow_cons, matBelow_cons]
        simp only [Nat.add_zero, Nat.zero_add]
        have hle : b.s + 2 * m ≤ b.s + 4 * m := by omega
        rw [max_eq_left (le_trans hle (le_max_right _ _))]
        rw [max_eq_right (show 0 ≤ 4 * m by omega)]
      have key := matBelow_tick (b :: bs) hinvb 0 0 m le_rfl (fun _ => rfl) hm g gs' hgs
      simp only [RT.den]
      rw [hmBelow]
      have hf : (fun gs => (⟨top.segs, top.trail - m⟩ : Seg).items (flatBelow true gs)) =
          (fun x => (⟨top.segs, top.trail - m⟩ : Seg).items x) ∘ flatBelow true := rfl
      rw [hf, ← Option.map_map, key, Option.map_map]
      simp only [flatBelow]
      rw [seg_sweep_items_C top hP hzt m]
      simp [h1, Function.comp_def]
    · simp [RT.tickN, hP, h1] at ht

end Sk1
