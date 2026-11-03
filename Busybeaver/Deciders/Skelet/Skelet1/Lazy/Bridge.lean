import Busybeaver.Deciders.Skelet.Skelet1.Cert.Steps
import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Certified

/-!
# Certified lazy runs and the eager machine

Certificate chunks are replayed on `RT`.  The subtype below carries the
representation invariant and a concrete denotation, so every checked event can
be lifted to a valid lazy state and then interpreted as an eager event.
-/

namespace Sk1

abbrev SafeRT := {t : RT // t.Good ∧ t.den.isSome}

def SafeRT.forget (t : SafeRT) : RT := t.1
def SafeRT.view (t : SafeRT) : List RI := RT.view t.1

def forgetSt (c : St SafeRT) : St RT := ⟨c.right, c.l, c.r.forget⟩
def viewSt (c : St SafeRT) : St (List RI) := ⟨c.right, c.l, c.r.view⟩

def embedSt (c : St RT) (h : c.r.Good ∧ c.r.den.isSome) : St SafeRT :=
  ⟨c.right, c.l, ⟨c.r, h⟩⟩

def SafeRT.wrapPop (s : SafeRT) : Option (RI × SafeRT) :=
  (checkedOps.pop s.1).attach.map fun p =>
    (p.1.1, ⟨p.1.2, checked_pop_good s.2.1 s.2.2 (by simpa using p.2)⟩)

def SafeRT.wrapTick (s : SafeRT) : Option SafeRT :=
  (checkedOps.tick s.1).attach.map fun p =>
    ⟨p.1, checked_tick_good s.2.1 s.2.2 (by simpa using p.2)⟩

def SafeRT.wrapTickN (n : Nat) (s : SafeRT) : Option SafeRT :=
  if hn : 0 < n then
    (checkedOps.tickN n s.1).attach.map fun p =>
      ⟨p.1, checked_tickN_good hn s.2.1 s.2.2 (by simpa using p.2)⟩
  else none

def safeOps : ROps SafeRT where
  pop := SafeRT.wrapPop
  push := fun s i => ⟨checkedOps.push s.1 i, checked_push_good s.2.1 s.2.2 i⟩
  tick := SafeRT.wrapTick
  tickN := SafeRT.wrapTickN
  toList := fun s => checkedOps.toList s.1
  ofList := fun xs => ⟨RT.ofList xs, ⟨RT.ofList_good xs, by
    rw [RT.ofList_den]
    rfl⟩⟩

theorem eager_toList (xs : List RI) : eagerOps.toList xs = some xs := rfl

theorem safe_toList_forget (s : SafeRT) : safeOps.toList s = checkedOps.toList s.1 := rfl

theorem safe_ofList_forget (xs : List RI) :
    SafeRT.forget (safeOps.ofList xs) = checkedOps.ofList xs := rfl

theorem uniSt_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hto : ∀ r, o₁.toList r = o₂.toList (f r))
    (hof : ∀ xs, f (o₁.ofList xs) = o₂.ofList xs) (c : St R) :
    (uniSt o₁ c).map (F.mapSt f) = uniSt o₂ (F.mapSt f c) := by
  cases c with
  | mk right l r =>
    cases right with
    | false => simp [uniSt, F.mapSt]
    | true =>
      cases l with
      | nil => simp [uniSt, F.mapSt]
      | cons x l =>
        cases x with
        | D =>
          cases l with
          | nil => simp [uniSt, F.mapSt]
          | cons x l =>
            cases x with
            | C1 =>
              cases l with
              | nil => simp [uniSt, F.mapSt]
              | cons x l =>
                cases x with
                | x a =>
                  simp only [uniSt, if_true, F.mapSt]
                  cases hstrip : stripP Jc l with
                  | none => simp [hstrip]
                  | some l' =>
                    rw [hto r]
                    cases hlist : o₂.toList (f r) with
                    | none => simp [hlist]
                    | some xs =>
                      cases hcount : uniCount a xs with
                      | zero => simp [hcount]
                      | succ k =>
                        cases hsweep : sweep 0 ((k + 1) * uniT) xs with
                        | none => simp [hcount, hsweep]
                        | some ys => simp [hcount, hsweep, hof, F.mapSt]
                | _ => simp [uniSt, F.mapSt]
            | _ => simp [uniSt, F.mapSt]
        | _ => simp [uniSt, F.mapSt]

theorem tickSt_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (htick : ∀ r, (o₁.tick r).map f = o₂.tick (f r)) (c : St R) :
    (tickSt o₁ c).map (F.mapSt f) = tickSt o₂ (F.mapSt f c) := by
  cases c with
  | mk right l r =>
    cases right with
    | false => simp [tickSt, F.mapSt]
    | true =>
      simp only [tickSt, if_true, F.mapSt, Option.map_map, Function.comp_def]
      have hm := congrArg (Option.map (fun x => (⟨false, l, x⟩ : St S))) (htick r)
      simpa only [Option.map_map, Function.comp_def] using hm

theorem safe_pop_forget (s : SafeRT) :
    F.mapPop SafeRT.forget (safeOps.pop s) = checkedOps.pop s.1 := by
  change F.mapPop SafeRT.forget (SafeRT.wrapPop s) = checkedOps.pop s.1
  cases hp : checkedOps.pop s.1 <;>
    simp [SafeRT.wrapPop, F.mapPop, SafeRT.forget, hp]

theorem safe_push_forget (s : SafeRT) (i : RI) :
    SafeRT.forget (safeOps.push s i) = checkedOps.push s.1 i := rfl

theorem safe_push_view (s : SafeRT) (i : RI) :
    SafeRT.view (safeOps.push s i) = eagerOps.push (SafeRT.view s) i := by
  change RT.view (checkedOps.push s.1 i) = eagerOps.push (RT.view s.1) i
  simpa [checkedOps, eagerOps] using RT.view_push s.1 i

theorem safe_tick_forget (s : SafeRT) :
    (safeOps.tick s).map SafeRT.forget = checkedOps.tick s.1 := by
  change (SafeRT.wrapTick s).map SafeRT.forget = checkedOps.tick s.1
  cases ht : checkedOps.tick s.1 <;>
    simp [SafeRT.wrapTick, SafeRT.forget, ht]

theorem safe_tickN_forget {n : Nat} (hn : 0 < n) (s : SafeRT) :
    (safeOps.tickN n s).map SafeRT.forget = checkedOps.tickN n s.1 := by
  change (SafeRT.wrapTickN n s).map SafeRT.forget = checkedOps.tickN n s.1
  cases ht : checkedOps.tickN n s.1 <;>
    simp [SafeRT.wrapTickN, SafeRT.forget, hn, ht]

theorem safe_toList_view (s : SafeRT) : safeOps.toList s = some s.view := by
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp s.2.2
  have hv := RT.view_eq_den s.2.1 hL
  simp [safeOps, checkedOps, SafeRT.view, hL, hv]

theorem safe_ofList_view (xs : List RI) : (safeOps.ofList xs).view = eagerOps.ofList xs := by
  apply RT.view_eq_den (RT.ofList_good xs)
  rw [RT.ofList_den]

theorem safe_simple_forget (c : St SafeRT) :
    (simple safeOps c).map (F.mapSt SafeRT.forget) = simple checkedOps (forgetSt c) := by
  have h := F.simple_map safeOps checkedOps SafeRT.forget safe_pop_forget safe_push_forget c
  change (simple safeOps c).map (F.mapSt SafeRT.forget) =
    simple checkedOps (F.mapSt SafeRT.forget c)
  simpa only [fast_simple_eq_simple] using h

theorem safe_simple_view (c : St SafeRT) :
    (simple safeOps c).map (F.mapSt SafeRT.view) = simple eagerOps (viewSt c) := by
  have hpop : ∀ s, F.mapPop SafeRT.view (safeOps.pop s) = eagerOps.pop (SafeRT.view s) := by
    intro s
    have hcomp : F.mapPop SafeRT.view (safeOps.pop s) =
        F.mapPop RT.view (F.mapPop SafeRT.forget (safeOps.pop s)) := by
      cases hp : safeOps.pop s with
      | none => rfl
      | some p => cases p; rfl
    calc
      F.mapPop SafeRT.view (safeOps.pop s) =
          F.mapPop RT.view (checkedOps.pop s.1) := by
            rw [hcomp, safe_pop_forget]
      _ = eagerOps.pop (RT.view s.1) := by
        have hp : checkedOps.pop s.1 = s.1.pop := by
          simp [checkedOps, s.2.2]
        rw [hp]
        exact RT.view_pop s.1 s.2.1.1
  have hpush : ∀ s i, SafeRT.view (safeOps.push s i) = eagerOps.push (SafeRT.view s) i := by
    exact safe_push_view
  have h := F.simple_map safeOps eagerOps SafeRT.view hpop hpush c
  change (simple safeOps c).map (F.mapSt SafeRT.view) =
    simple eagerOps (F.mapSt SafeRT.view c)
  simpa only [fast_simple_eq_simple] using h

theorem safe_tick_sound {s s' : SafeRT} (h : safeOps.tick s = some s') :
    eagerOps.tick s.view = some s'.view := by
  have hc : checkedOps.tick s.1 = some s'.1 := by
    have := safe_tick_forget s
    rw [h] at this
    simpa [SafeRT.forget] using this.symm
  have ht : s.1.tick = some s'.1 := by
    unfold checkedOps at hc
    cases hraw : s.1.tick with
    | none => simp [hraw] at hc
    | some t =>
      simp only [hraw] at hc
      split at hc
      · simpa only [Option.some.injEq] using hc
      · simp at hc
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp s.2.2
  have hv := RT.view_eq_den s.2.1 hL
  have hd := RT.tick_den s.1 s'.1 s.2.1.1 L hL ht
  cases hsweep : sweep 0 1 L with
  | none =>
    have hvld := s'.2.2
    rw [hd, hsweep] at hvld
    simp at hvld
  | some L' =>
    have hd' : s'.1.den = some L' := by simpa [hsweep] using hd
    have hv' := RT.view_eq_den s'.2.1 hd'
    change sweep 0 1 (RT.view s.1) = some (RT.view s'.1)
    rw [hv, hv']
    simp [eagerOps, hsweep]

theorem safe_tickN_sound {n : Nat} (hn : 0 < n) {s s' : SafeRT}
    (h : safeOps.tickN n s = some s') : eagerOps.tickN n s.view = some s'.view := by
  have hc : checkedOps.tickN n s.1 = some s'.1 := by
    have := safe_tickN_forget hn s
    rw [h] at this
    simpa [SafeRT.forget] using this.symm
  have ht : s.1.tickN n = some s'.1 := by
    unfold checkedOps at hc
    cases hraw : s.1.tickN n with
    | none => simp [hraw] at hc
    | some t =>
      simp only [hraw] at hc
      split at hc
      · simpa only [Option.some.injEq] using hc
      · simp at hc
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp s.2.2
  have hv := RT.view_eq_den s.2.1 hL
  have hd := RT.tickN_den s.1 s'.1 n hn s.2.1.1 L hL ht
  cases hsweep : sweep 0 n L with
  | none =>
    have hvld := s'.2.2
    rw [hd, hsweep] at hvld
    simp at hvld
  | some L' =>
    have hd' : s'.1.den = some L' := by simpa [hsweep] using hd
    have hv' := RT.view_eq_den s'.2.1 hd'
    change sweep 0 n (RT.view s.1) = some (RT.view s'.1)
    rw [hv, hv']
    simp [eagerOps, hsweep]

theorem safe_tickSt_sound {c c' : St SafeRT} (h : tickSt safeOps c = some c') :
    tickSt eagerOps (viewSt c) = some (viewSt c') := by
  cases c with
  | mk right l r =>
    cases right with
    | false => simp [tickSt] at h
    | true =>
      unfold tickSt at h ⊢
      simp only [if_true] at h
      cases ht : safeOps.tick r with
      | none => simp [ht] at h
      | some r' =>
        simp only [ht, Option.map_some, Option.some.injEq] at h
        subst c'
        have hte := safe_tick_sound ht
        simpa [tickSt, eagerOps, viewSt, SafeRT.view, hte]

theorem safe_uniSt_sound {c c' : St SafeRT} (h : uniSt safeOps c = some c') :
    uniSt eagerOps (viewSt c) = some (viewSt c') := by
  have hto : ∀ s : SafeRT, safeOps.toList s = eagerOps.toList (SafeRT.view s) := by
    intro s
    rw [safe_toList_view, eager_toList]
  have hm := uniSt_map safeOps eagerOps SafeRT.view hto safe_ofList_view c
  simpa [h, viewSt, F.mapSt, SafeRT.view] using hm.symm

theorem safe_ev_forget (e : Nat) (c : St SafeRT) :
    (ev safeOps e c).map (F.mapSt SafeRT.forget) = ev checkedOps e (forgetSt c) := by
  cases e with
  | zero => simpa [ev] using safe_simple_forget c
  | succ e =>
    cases e with
    | zero =>
      have ht : ∀ r : SafeRT, (safeOps.tick r).map SafeRT.forget =
          checkedOps.tick (SafeRT.forget r) := safe_tick_forget
      have hm := tickSt_map safeOps checkedOps SafeRT.forget ht c
      simpa [ev, forgetSt, F.mapSt] using hm
    | succ e =>
      have hu := uniSt_map safeOps checkedOps SafeRT.forget
        safe_toList_forget safe_ofList_forget c
      simpa [ev, forgetSt, F.mapSt] using hu

theorem safe_event_forget {e : Nat} (c : St SafeRT) :
    (ev safeOps e c).map (F.mapSt SafeRT.forget) = ev checkedOps e (forgetSt c) :=
  safe_ev_forget e c

theorem safe_step_forget {c c' : St RT} (s : St SafeRT) (hs : forgetSt s = c)
    (h : Step checkedOps c c') :
    ∃ s', forgetSt s' = c' ∧ Step safeOps s s' := by
  obtain ⟨e, he⟩ := h
  have he' : (ev safeOps e s).map (F.mapSt SafeRT.forget) = some c' := by
    rw [safe_event_forget, hs]
    exact he
  obtain ⟨s', hstep, hproj⟩ := Option.map_eq_some_iff.mp he'
  exact ⟨s', hproj, e, hstep⟩

theorem checked_steps_lift {c c' : St RT} (h : Steps checkedOps c c')
    (hc : c.r.Good ∧ c.r.den.isSome) :
    ∃ s', forgetSt s' = c' ∧ Steps safeOps (embedSt c hc) s' := by
  induction h with
  | refl => exact ⟨embedSt c hc, rfl, .refl⟩
  | @tail a b hab hbd ih =>
    obtain ⟨s, hs, hp⟩ := ih
    obtain ⟨s', hs', hsStep⟩ := safe_step_forget s hs hbd
    exact ⟨s', hs', hp.trans (Relation.ReflTransGen.single hsStep)⟩

theorem safe_step_sound {c c' : St SafeRT} (h : Step safeOps c c') :
    Step eagerOps (viewSt c) (viewSt c') := by
  obtain ⟨e, he⟩ := h
  cases e with
  | zero =>
    have hsimp : simple safeOps c = some c' := by simpa [ev] using he
    have hm := safe_simple_view c
    rw [hsimp] at hm
    have hsimple : simple eagerOps (viewSt c) = some (viewSt c') := by
      simpa [viewSt, F.mapSt, SafeRT.view] using hm.symm
    exact ⟨0, by simpa [ev] using hsimple⟩
  | succ e =>
    cases e with
    | zero =>
      have ht : tickSt eagerOps (viewSt c) = some (viewSt c') := safe_tickSt_sound he
      exact ⟨1, by simpa [ev] using ht⟩
    | succ e =>
      have hu : uniSt eagerOps (viewSt c) = some (viewSt c') := safe_uniSt_sound he
      exact ⟨e + 2, by simpa [ev] using hu⟩

theorem safe_steps_sound {c c' : St SafeRT} (h : Steps safeOps c c') :
    Steps eagerOps (viewSt c) (viewSt c') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (Relation.ReflTransGen.single (safe_step_sound hs))

theorem checked_steps_sound {c c' : St RT} (h : Steps checkedOps c c')
    (hc : c.r.Good ∧ c.r.den.isSome) :
    Steps eagerOps ⟨c.right, c.l, RT.view c.r⟩ ⟨c'.right, c'.l, RT.view c'.r⟩ := by
  obtain ⟨s', hs', hp⟩ := checked_steps_lift h hc
  have he := safe_steps_sound hp
  have hend : viewSt s' = ⟨c'.right, c'.l, RT.view c'.r⟩ := by
    cases hs'
    rfl
  have hstart : viewSt (embedSt c hc) = ⟨c.right, c.l, RT.view c.r⟩ := rfl
  rw [← hend, ← hstart]
  exact he

theorem checked_init_steps_sound {c' : St RT} (h : Steps checkedOps (⟨true, [.C1], RT.ofList [.P]⟩ : St RT) c')
    (hc : c'.r.Good ∧ c'.r.den.isSome) :
    Steps eagerOps Sk1.init ⟨c'.right, c'.l, RT.view c'.r⟩ := by
  have hs := checked_steps_sound h ⟨RT.ofList_good [.P], by rw [RT.ofList_den]; rfl⟩
  have hi : RT.view (RT.ofList [.P]) = [.P] := by
    apply RT.view_eq_den (RT.ofList_good [.P])
    rw [RT.ofList_den]
    simp [eagerOps, ePush]
  have hstart : (⟨true, [.C1], RT.view (RT.ofList [.P])⟩ : St (List RI)) = Sk1.init := by
    simp [Sk1.init, hi]
  rw [hstart] at hs
  exact hs

end Sk1
