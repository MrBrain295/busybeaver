import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Raw
import Busybeaver.Deciders.Skelet.Skelet1.Lazy.FastHom

/-!
# Checked lazy operations

The event certificates run on the deferred tape.  A batched tick is accepted
only when its result still has a concrete eager denotation; this makes every
certified event a genuine step of the eager symbolic machine.
-/

namespace Sk1

def checkedOps : ROps RT where
  pop := RT.pop
  push := RT.push
  tick := fun t =>
    match t.tick with
    | none => none
    | some t' => if t'.den.isSome then some t' else none
  tickN := fun n t =>
    match t.tickN n with
    | none => none
    | some t' => if t'.den.isSome then some t' else none
  toList := RT.den
  ofList := RT.ofList

theorem checked_pop_view {t : RT} (hgood : t.Good) (hvalid : t.den.isSome) :
    F.mapPop RT.view (checkedOps.pop t) = eagerOps.pop (RT.view t) := by
  simpa [checkedOps, F.mapPop] using RT.view_pop t hgood.1

theorem checked_push_view (t : RT) (i : RI) :
    RT.view (checkedOps.push t i) = eagerOps.push (RT.view t) i := by
  simpa [checkedOps, eagerOps] using RT.view_push t i

theorem checked_pop_good {t t' : RT} {i : RI} (hgood : t.Good) (hvalid : t.den.isSome)
    (h : checkedOps.pop t = some (i, t')) : t'.Good ∧ t'.den.isSome := by
  have hp : t.pop = some (i, t') := by
    simpa [checkedOps] using h
  have hg := RT.good_pop t t' i hgood hp
  have hden : t.den.isSome := hvalid
  cases hd : t.den with
  | none => simp [hd] at hden
  | some L =>
    have hpop := RT.pop_den t t' i hgood.1 hp
    cases hdt : t'.den with
    | none => simp [hd, hdt] at hpop
    | some L' => exact ⟨hg, by simp [hdt]⟩

theorem checked_push_good {t : RT} (hgood : t.Good) (hvalid : t.den.isSome) (i : RI) :
    (checkedOps.push t i).Good ∧ (checkedOps.push t i).den.isSome := by
  have hg := RT.good_push t hgood i
  cases hd : t.den with
  | none => simp [hd] at hvalid
  | some L =>
    refine ⟨hg, ?_⟩
    change (t.push i).den.isSome
    rw [RT.push_den, hd]
    rfl

theorem checked_tick_good {t t' : RT} (hgood : t.Good) (hvalid : t.den.isSome)
    (h : checkedOps.tick t = some t') : t'.Good ∧ t'.den.isSome := by
  unfold checkedOps at h
  cases ht : t.tick with
  | none => simp [ht] at h
  | some u =>
    simp only [ht] at h
    cases hu : u.den.isSome with
    | false => simp [hu] at h
    | true =>
      simp only [hu] at h
      have hEq : u = t' := Option.some.inj h
      rw [← hEq]
      exact ⟨RT.good_tick t u hgood ht, hu⟩

theorem checked_tickN_good {t t' : RT} {m : Nat} (hm : 0 < m)
    (hgood : t.Good) (hvalid : t.den.isSome) (h : checkedOps.tickN m t = some t') :
    t'.Good ∧ t'.den.isSome := by
  unfold checkedOps at h
  cases ht : t.tickN m with
  | none => simp [ht] at h
  | some u =>
    simp only [ht] at h
    cases hu : u.den.isSome with
    | false => simp [hu] at h
    | true =>
      simp only [hu] at h
      have hEq : u = t' := Option.some.inj h
      rw [← hEq]
      exact ⟨RT.good_tickN t u m hm hgood ht, hu⟩

end Sk1
