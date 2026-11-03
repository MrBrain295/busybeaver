import Busybeaver.Deciders.Skelet.Skelet1.Cert.Steps
import Busybeaver.Deciders.Skelet.Skelet1.K.K4

/-!
# Truncated left tapes

Certificate segments keep only the top of the left tape, followed by the marker
`tl` standing for the rest.  No rule can create `tl`, every rule fails or
destroys `tl` when it would have to inspect it (see `lx` in `Sim.lean`), so a run
that ends with the marker still present never looked below it: it is valid for
every actual tail.
-/

namespace Sk1

/-- Replace the (first) tail marker of a left tape by an actual tail `T`. -/
def substT (T : List LS) : List LS → List LS
  | [] => []
  | .tl :: _ => T
  | s :: l => s :: substT T l

/-! ## Basic facts about `substT` -/

section
variable (T : List LS)

@[simp] theorem substT_nil : substT T [] = [] := rfl

@[simp] theorem substT_tl (l : List LS) : substT T (.tl :: l) = T := rfl

@[simp] theorem substT_cons {s : LS} (hs : s ≠ .tl) (l : List LS) :
    substT T (s :: l) = s :: substT T l := by
  cases s <;> first | rfl | exact absurd rfl hs

theorem substT_of_not_mem {l : List LS} (h : LS.tl ∉ l) : substT T l = l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs : s ≠ .tl := fun e => h (e ▸ List.mem_cons_self ..)
    rw [substT_cons T hs, ih (fun hl => h (List.mem_cons_of_mem _ hl))]

theorem substT_append {A : List LS} (hA : LS.tl ∉ A) (l : List LS) :
    substT T (A ++ l) = A ++ substT T l := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    have hs : s ≠ .tl := fun e => hA (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, substT_cons T hs, ih (fun hl => hA (List.mem_cons_of_mem _ hl)),
      List.cons_append]

theorem not_mem_substT {l : List LS} (hT : LS.tl ∉ T) : LS.tl ∉ substT T l := by
  induction l with
  | nil => simp
  | cons s l ih =>
    by_cases hs : s = .tl
    · subst hs; simpa using hT
    · rw [substT_cons T hs]; simp [Ne.symm hs, ih]

theorem lx_frame {n : Nat} {l : List LS} (h : LS.tl ∈ lx n l) :
    LS.tl ∈ l ∧ substT T (lx n l) = lx n (substT T l) := by
  unfold lx at h ⊢
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte] at h ⊢; exact ⟨h, trivial⟩
  · simp only [hn, ↓reduceIte] at h ⊢
    rcases l with _ | ⟨s, l⟩
    · simp at h
    · cases s <;> simp_all

theorem lF_frame {n : Nat} {l : List LS} (h : LS.tl ∈ lF n l) :
    LS.tl ∈ l ∧ substT T (lF n l) = lF n (substT T l) := by
  unfold lF at h ⊢
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte] at h ⊢; exact ⟨h, trivial⟩
  · simp only [hn, ↓reduceIte] at h ⊢
    rcases l with _ | ⟨s, l⟩
    · simp at h
    · cases s <;> simp_all

theorem lG_frame {n : Nat} {l : List LS} (h : LS.tl ∈ lG n l) :
    LS.tl ∈ l ∧ substT T (lG n l) = lG n (substT T l) := by
  unfold lG at h ⊢
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte] at h ⊢; exact ⟨h, trivial⟩
  · simp only [hn, ↓reduceIte] at h ⊢
    rcases l with _ | ⟨s, l⟩
    · simp at h
    · cases s <;> simp_all

theorem lH_frame {n : Nat} {l : List LS} (h : LS.tl ∈ lH n l) :
    LS.tl ∈ l ∧ substT T (lH n l) = lH n (substT T l) := by
  unfold lH at h ⊢
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte] at h ⊢; exact ⟨h, trivial⟩
  · simp only [hn, ↓reduceIte] at h ⊢
    rcases l with _ | ⟨s, l⟩
    · simp at h
    · cases s <;> simp_all

end

theorem stripP_eq {A l l' : List LS} (h : stripP A l = some l') : l = A ++ l' := by
  induction A generalizing l with
  | nil => simp only [stripP, Option.some.injEq] at h; simp [h]
  | cons a A ih =>
    rcases l with _ | ⟨b, l⟩
    · simp [stripP] at h
    · simp only [stripP] at h
      split_ifs at h with hab
      subst hab
      rw [ih h]
      rfl

theorem stripP_append (A l : List LS) : stripP A (A ++ l) = some l := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [stripP, ih]

theorem tl_not_mem_Jc : LS.tl ∉ Jc := by decide

section
variable {R : Type} (o : ROps R) (T : List LS)

theorem simple_frame {c c' : St R} (hs : simple o c = some c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧ simple o ⟨c.right, substT T c.l, c.r⟩ = some ⟨c'.right, substT T c'.l, c'.r⟩ := by
  obtain ⟨d, l, r⟩ := c
  cases d
  · simp only [simple, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rcases l with _ | ⟨s, l⟩
    · exfalso
      simp only at hs
      split at hs
      · obtain ⟨r4, hr4, rfl⟩ := Option.map_eq_some_iff.mp hs
        simp at h
      · cases hs
    · cases s
      case F3 =>
        rcases l with _ | ⟨s, l⟩
        · simp at hs
        · cases s
          case x n =>
            rcases n with _ | n
            · simp at hs
            · simp at hs; subst hs; simp at h
              obtain ⟨h1, h2⟩ := lx_frame T h
              simp [h1, h2]
          all_goals simp at hs
      all_goals simp at hs
      all_goals (subst hs; simp_all)
  · simp only [simple, ↓reduceIte] at hs ⊢
    rcases hp : o.pop r with _ | ⟨i, r1⟩
    · simp only [hp] at hs ⊢
      rcases l with _ | ⟨s, l⟩
      · simp at hs
      · cases s
        case x n =>
          rcases n with _ | n
          · simp at hs
          · simp at hs; subst hs; simp at h
            obtain ⟨h1, h2⟩ := lx_frame T h
            simp [h1, h2]
        all_goals simp at hs
        all_goals (subst hs; simp_all)
    · simp only [hp] at hs ⊢
      cases i
      case x n =>
        simp at hs; subst hs; simp at h
        obtain ⟨h1, h2⟩ := lx_frame T h
        simp [h1, h2]
      case D => simp at hs; subst hs; simp_all
      case G n =>
        simp at hs; subst hs; simp at h
        obtain ⟨h1, h2⟩ := lG_frame T h
        simp [h1, h2]
      case C =>
        rcases l with _ | ⟨s, l⟩
        · simp at hs
        · cases s
          case x n =>
            rcases n with _ | n
            · simp at hs
            · simp at hs; subst hs; simp at h
              obtain ⟨h1, h2⟩ := lx_frame T h
              simp [h1, h2]
          all_goals simp at hs
          all_goals (subst hs; simp_all)
      case P =>
        simp only at hs ⊢
        rcases hp2 : o.pop r1 with _ | ⟨i2, r2⟩
        · simp only [hp2] at hs ⊢
          cases hs; simp_all
        · simp only [hp2] at hs ⊢
          cases i2
          case x n =>
            simp at hs; subst hs; simp at h
            obtain ⟨h1, h2⟩ := lx_frame T h
            simp [h1, h2]
          case P =>
            simp at hs; subst hs; simp at h
            obtain ⟨h1, h2⟩ := lx_frame T h
            simp [h1, h2]
          case G n => simp at hs
          case C =>
            simp only at hs ⊢
            obtain ⟨r3, hr3, rfl⟩ := Option.map_eq_some_iff.mp hs
            simp at h; simp [hr3, h]
          case D =>
            simp only at hs ⊢
            rcases hp3 : o.pop r2 with _ | ⟨i3, r3⟩
            · simp [hp3] at hs
            · simp only [hp3] at hs ⊢
              cases i3
              case x n =>
                rcases n with _ | n
                · simp at hs
                · simp at hs; subst hs; simp_all
              case D =>
                simp only at hs ⊢
                obtain ⟨r4, hr4, rfl⟩ := Option.map_eq_some_iff.mp hs
                simp at h; simp [hr4, h]
              case C =>
                simp only at hs ⊢
                obtain ⟨r4, hr4, rfl⟩ := Option.map_eq_some_iff.mp hs
                simp at h; simp [hr4, h]
              case P => simp at hs; subst hs; simp_all
              case G n =>
                simp at hs; subst hs; simp at h
                obtain ⟨h1, h2⟩ := lH_frame T h
                simp [h1, h2]

theorem tickSt_frame {c c' : St R} (hs : tickSt o c = some c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧ tickSt o ⟨c.right, substT T c.l, c.r⟩ = some ⟨c'.right, substT T c'.l, c'.r⟩ := by
  obtain ⟨d, l, r⟩ := c
  unfold tickSt at hs ⊢
  split at hs
  · rename_i hd
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hs
    simp only at hd h ⊢
    simp [hd, hr', h]
  · cases hs

theorem uniSt_frame {c c' : St R} (hs : uniSt o c = some c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧ uniSt o ⟨c.right, substT T c.l, c.r⟩ = some ⟨c'.right, substT T c'.l, c'.r⟩ := by
  obtain ⟨d, l, r⟩ := c
  unfold uniSt at hs ⊢
  split at hs
  · rename_i hd
    simp only at hd; subst hd
    split at hs
    · rename_i a l0 hl
      simp only at hl; subst hl
      split at hs
      · rename_i l1 hstrip
        split at hs
        · rename_i rl hrl
          split at hs
          · cases hs
          · rename_i k hk
            split at hs
            · rename_i r' hsw
              cases hs
              have := stripP_eq hstrip; subst this
              simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or,
                tl_not_mem_Jc] at h
              obtain ⟨h1, h2⟩ := lF_frame T h
              simp [substT_append T tl_not_mem_Jc, stripP_append, h1, h2, hrl, hk, hsw]
            · cases hs
        · cases hs
      · cases hs
    · cases hs
  · cases hs

theorem uniKSt_frame {k : Nat} {c c' : St R} (hs : uniKSt o k c = some c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧
      uniKSt o k ⟨c.right, substT T c.l, c.r⟩ = some ⟨c'.right, substT T c'.l, c'.r⟩ := by
  obtain ⟨d, l, r⟩ := c
  unfold uniKSt at hs ⊢
  split at hs
  · rename_i hd
    simp only at hd; subst hd
    split at hs
    · rename_i a l0 hl
      simp only at hl; subst hl
      split at hs
      · rename_i l1 hstrip
        split at hs
        · rename_i hk
          split at hs
          · rename_i r' hsw
            cases hs
            have := stripP_eq hstrip; subst this
            simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or,
              tl_not_mem_Jc] at h
            obtain ⟨h1, h2⟩ := lF_frame T h
            simp [substT_append T tl_not_mem_Jc, stripP_append, h1, h2, hk, hsw]
          · cases hs
        · cases hs
      · cases hs
    · cases hs
  · cases hs

theorem ev_frame {e : Nat} {c c' : St R} (hs : ev o e c = some c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧ ev o e ⟨c.right, substT T c.l, c.r⟩ = some ⟨c'.right, substT T c'.l, c'.r⟩ := by
  match e, hs with
  | 0, hs => exact simple_frame o T hs h
  | 1, hs => exact tickSt_frame o T hs h
  | _ + 2, hs => exact uniSt_frame o T hs h

/-- One event, with the tail marker kept: the marker was there before, and the event is
valid with any tail in its place. -/
theorem step_frame {c c' : St R} (hs : Step o c c') (h : LS.tl ∈ c'.l) :
    LS.tl ∈ c.l ∧ Step o ⟨c.right, substT T c.l, c.r⟩ ⟨c'.right, substT T c'.l, c'.r⟩ := by
  unfold Step at hs ⊢
  obtain ⟨e, he⟩ := hs
  obtain ⟨h1, h2⟩ := ev_frame o T he h
  exact ⟨h1, e, h2⟩

/-- No event creates the tail marker. -/
theorem steps_tl {c c' : St R} (hs : Steps o c c') (h : LS.tl ∈ c'.l) : LS.tl ∈ c.l := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact ih (step_frame o [] hst h).1

theorem steps_frame_aux {c c' : St R} (hs : Steps o c c') (h : LS.tl ∈ c'.l) :
    Steps o ⟨c.right, substT T c.l, c.r⟩ ⟨c'.right, substT T c'.l, c'.r⟩ := by
  induction hs with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨h1, h2⟩ := step_frame o T hst h
    exact Relation.ReflTransGen.tail (ih h1) h2

end

/-- **Frame property.** A run that keeps the tail marker is valid with any
tail in its place. -/
theorem steps_frame {R : Type} {o : ROps R} {c c' : St R} (h : Steps o c c') (T : List LS)
    (htl : LS.tl ∈ c.l → LS.tl ∈ c'.l) :
    Steps o ⟨c.right, substT T c.l, c.r⟩ ⟨c'.right, substT T c'.l, c'.r⟩ := by
  by_cases hc : LS.tl ∈ c.l
  · exact steps_frame_aux o T h (htl hc)
  · have hc' : LS.tl ∉ c'.l := fun h' => hc (steps_tl o h h')
    rw [substT_of_not_mem T hc, substT_of_not_mem T hc']
    exact h

/-- The gluing check between consecutive segments is sound. -/
theorem glueL_sound {b a : List LS} (h : K4.glueL b a = true) (X : List LS) (hX : LS.tl ∉ X) :
    ∃ X', LS.tl ∉ X' ∧ substT X b = substT X' a := by
  induction b, a using K4.glueL.induct with
  | case1 t => exact ⟨substT X t, not_mem_substT X hX, rfl⟩
  | case2 x b y a hne ih =>
    rw [K4.glueL.eq_2 x b y a hne, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    by_cases hx : x = .tl
    · subst hx; exact ⟨X, hX, rfl⟩
    · obtain ⟨X', hX', he⟩ := ih h
      exact ⟨X', hX', by rw [substT_cons X hx, substT_cons X' hx, he]⟩
  | case3 => exact ⟨X, hX, rfl⟩
  | case4 t x h1 h2 h3 => rw [K4.glueL.eq_4 t x h1 h2 h3] at h; cases h

end Sk1
