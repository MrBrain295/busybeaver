import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Correct
import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-!
# Push, pop and the invariant of the lazy right tape

Together with `Sk1.RT.tick_den` this shows that the lazy right tape is a faithful
implementation of the eager right tape: `RT.den` commutes with every operation.
-/

namespace Sk1

/-- Push one item on an eager right tape (runs and `G` blocks merge). -/
def pushItem : RI → List RI → List RI
  | .x n, t => pushX n t
  | .D, t => .D :: t
  | .C, t => .C :: t
  | .P, t => .P :: t
  | .G n, t => pushG n t

theorem pushItem_sep (sp : Sep) (t : List RI) : pushItem sp.item t = sp.push t := by
  cases sp <;> rfl

theorem matBelow_addPend (tp : Bool) (s r : Nat) (h : s ≤ r) (bs : List LBlk) :
    matBelow tp 0 0 (addPend s r bs) = matBelow tp s r bs := by
  rcases bs with _ | ⟨b, bs⟩
  · rfl
  · simp only [addPend]
    rw [matBelow_cons, matBelow_cons]
    simp only
    have e : max (max b.r (b.s + r)) (b.s + s) = max b.r (b.s + r) := by omega
    simp only [Nat.add_zero, e]

theorem addPend_inv (s r : Nat) (h1 : s ≤ r) (h2 : s = 0 → r = 0) (bs : List LBlk)
    (h : ∀ b ∈ bs, b.Inv) : ∀ b ∈ addPend s r bs, b.Inv := by
  rcases bs with _ | ⟨b, bs⟩
  · simp [addPend]
  · intro c hc
    simp only [addPend, List.mem_cons] at hc
    obtain ⟨hz, hb1, hb2⟩ := h b (List.mem_cons_self ..)
    rcases hc with rfl | hc
    · exact ⟨hz, by simp only; omega, by simp only; omega⟩
    · exact h c (List.mem_cons_of_mem _ hc)

/-! ## Push -/

theorem RT.push_den (t : RT) (i : RI) : (t.push i).den = t.den.map (pushItem i) := by
  obtain ⟨top, below, termP⟩ := t
  cases i with
  | x n =>
    simp only [RT.push, RT.den, Option.map_map, Function.comp_def, pushItem, seg_items_pushX]
  | D =>
    simp only [RT.push, RT.den, Option.map_map, Function.comp_def, pushItem]
    rfl
  | G n =>
    simp only [RT.push, RT.den, Option.map_map, Function.comp_def, pushItem]
    congr 1; funext gs
    obtain ⟨segs, tr⟩ := top
    by_cases hn : n = 0
    · subst hn; simp [Seg.pushG, pushG]
    · simp only [Seg.pushG, hn, ite_false]
      split
      · simp [seg_items_cons, pushX_zero, Sep.push, pushG_pushG]
      · simp [seg_items_cons, pushX_zero, Sep.push]
  | P =>
    simp only [RT.push]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨segs, tr⟩ := top
      simp only [Seg.isEmpty, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp only [List.isEmpty_iff] at h2
      subst h2; subst h3
      rfl
    · simp only [RT.den, Option.map_map, Function.comp_def, pushItem]
      rfl
  | C =>
    simp only [RT.push, RT.den, Option.map_map, Function.comp_def, pushItem]
    rw [matBelow_cons]
    simp [Seg.apply, Option.map_map, Function.comp_def, flatBelow, seg_items_nil, pushX_zero]

theorem RT.push_inv (t : RT) (hinv : t.Inv) (i : RI) : (t.push i).Inv := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hz, hb⟩ := hinv
  obtain ⟨segs, tr⟩ := top
  cases i with
  | x n =>
    refine ⟨?_, hb⟩
    simp only [RT.push, Seg.pushX]
    split
    · exact hz
    · split
      · intro p hp; simp at hp
      · simp_all [Seg.NZ] ; exact hz.2
  | D =>
    refine ⟨?_, hb⟩
    intro p hp
    simp only [RT.push, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · exact hz _ hp
  | G n =>
    refine ⟨?_, hb⟩
    simp only [RT.push, Seg.pushG]
    split
    · exact hz
    · rename_i hn
      split
      · simp_all [Seg.NZ] ; exact hz.2
      · simp_all [Seg.NZ] ; exact hz
  | P =>
    simp only [RT.push]
    split
    · exact ⟨hz, hb⟩
    · refine ⟨?_, hb⟩
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact hz _ hp
  | C =>
    refine ⟨fun p hp => by simp [RT.push] at hp, ?_⟩
    intro b hb'
    simp only [RT.push, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ⟨hz, le_rfl, fun _ => rfl⟩
    · exact hb b hb'

/-! ## Pop (including the materialization of a deferred level) -/

theorem RT.pop_den (t t' : RT) (i : RI) (hinv : t.Inv) (h : t.pop = some (i, t')) :
    t.den = t'.den.map (pushItem i) := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hz, hb⟩ := hinv
  obtain ⟨segs, tr⟩ := top
  simp only [RT.pop] at h
  rcases segs with _ | ⟨⟨a, sp⟩, rest⟩
  · simp only at h
    by_cases htr : tr = 0
    · subst htr
      simp only [ite_true] at h
      rcases below with _ | ⟨b, bs⟩
      · cases termP
        · simp at h
        · simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
      · simp only at h
        split at h
        · rename_i g hg
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨_, hb1, _⟩ := hb b (List.mem_cons_self ..)
          simp only [RT.den, Option.map_map, Function.comp_def]
          rw [matBelow_cons, matBelow_addPend _ _ _ (by omega)]
          have e : max b.r b.s = b.r := by omega
          simp only [Nat.add_zero, e, hg, Option.bind_some, Option.map_map, Function.comp_def]
          rfl
        · simp at h
    · simp only [htr, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [RT.den, Option.map_map, Function.comp_def, pushItem]
      rfl
  · simp only at h
    by_cases ha : a = 0
    · subst ha
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [RT.den, Option.map_map, Function.comp_def, pushItem_sep]
      rfl
    · simp only [ha, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [RT.den, Option.map_map, Function.comp_def, pushItem]
      rfl

theorem RT.pop_inv (t t' : RT) (i : RI) (hinv : t.Inv) (h : t.pop = some (i, t')) : t'.Inv := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hz, hb⟩ := hinv
  obtain ⟨segs, tr⟩ := top
  simp only [RT.pop] at h
  rcases segs with _ | ⟨⟨a, sp⟩, rest⟩
  · simp only at h
    by_cases htr : tr = 0
    · subst htr
      simp only [ite_true] at h
      rcases below with _ | ⟨b, bs⟩
      · cases termP
        · simp at h
        · simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hz, by simp⟩
      · simp only at h
        split at h
        · rename_i g hg
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbz, hb1, hb2⟩ := hb b (List.mem_cons_self ..)
          exact ⟨seg_apply_NZ _ _ _ _ _ _ hbz hg,
            addPend_inv _ _ (by omega) (by omega) bs
              (fun c hc => hb c (List.mem_cons_of_mem _ hc))⟩
        · simp at h
    · simp only [htr, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun p hp => by simp at hp, hb⟩
  · simp only at h
    by_cases ha : a = 0
    · subst ha
      simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun p hp => hz p (List.mem_cons_of_mem _ hp), hb⟩
    · simp only [ha, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hb⟩
      simp_all [Seg.NZ] ; exact hz.2

/-! ## Tick preserves the invariant -/

theorem RT.tick_inv (t t' : RT) (hinv : t.Inv) (h : t.tick = some t') : t'.Inv := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hz, hb⟩ := hinv
  simp only [RT.tick] at h
  split at h
  · split at h
    · simp at h
    · split at h
      · cases h; exact ⟨hz, hb⟩
      · rename_i b bs
        split at h
        · cases h
          obtain ⟨hbz, hb1, hb2⟩ := hb b (List.mem_cons_self ..)
          refine ⟨hz, ?_⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨hbz, by simp only; omega, by simp only; omega⟩
          · exact hb c (List.mem_cons_of_mem _ hc)
        · simp at h
  · simp at h

theorem RT.tickN_inv (t t' : RT) (m : Nat) (hm : 0 < m) (hinv : t.Inv)
    (h : RT.tickN m t = some t') : t'.Inv := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨htop, hbelow⟩ := hinv
  simp only [RT.tickN] at h
  split at h
  · split at h
    · simp at h
    · split at h
      · cases h
        exact ⟨htop, hbelow⟩
      · rename_i b bs
        split at h
        · cases h
          refine ⟨htop, ?_⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · obtain ⟨hbz, hbs, hb0⟩ := hbelow b (List.mem_cons_self ..)
            change b.body.NZ ∧ b.s + 2 * m ≤ max b.r (b.s + 4 * m) ∧
              (b.s + 2 * m = 0 → max b.r (b.s + 4 * m) = 0)
            exact ⟨hbz, by omega, by intro he; omega⟩
          · exact hbelow c (List.mem_cons_of_mem _ hc)
        · simp at h
  · simp at h

theorem RT.ofList_inv (xs : List RI) : (RT.ofList xs).Inv := by
  induction xs with
  | nil => simp [RT.ofList, RT.Inv, Seg.NZ]
  | cons i xs ih =>
    simp only [RT.ofList, List.foldr_cons]
    exact RT.push_inv (RT.ofList xs) ih i

theorem pushItem_eq_ePush (i : RI) (xs : List RI) : pushItem i xs = ePush xs i := by
  cases i <;> rfl

theorem RT.ofList_den (xs : List RI) :
    (RT.ofList xs).den = some (eagerOps.ofList xs) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change ((RT.ofList xs).push i).den = some (ePush (eagerOps.ofList xs) i)
    rw [RT.push_den, ih]
    simp [pushItem_eq_ePush]

end Sk1
