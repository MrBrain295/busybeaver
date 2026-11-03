import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Fast

namespace Sk1.F

def mapSt (f : R → S) (c : St R) : St S := ⟨c.right, c.l, f c.r⟩

def mapPop (f : R → S) : Option (RI × R) → Option (RI × S) :=
  Option.map fun p => (p.1, f p.2)

theorem foldPush_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) :
    ∀ (is : List RI) (r : R),
      f (is.foldr (fun i t => o₁.push t i) r) = is.foldr (fun i t => o₂.push t i) (f r)
  | [], r => rfl
  | i :: is, r => by simp [List.foldr, foldPush_map o₁ o₂ f hpush is, hpush]

theorem unx_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (r : R) :
    (unx o₁ r).map f = unx o₂ (f r) := by
  unfold unx
  rw [← hpop r]
  cases hp : o₁.pop r with
  | none => simp [mapPop, hp]
  | some p =>
    obtain ⟨i, r'⟩ := p
    cases i with
    | x n => cases n <;> simp [mapPop, hp, hpush]
    | G n =>
      cases n with
      | zero => simp [mapPop, hp]
      | succ n =>
        simp only [mapPop, hp, Option.map_some]
        have hfold := foldPush_map o₁ o₂ f hpush
          [.x 299, .D, .x 30826, .D, .x 72142, .D, .x 3076, .D, .x 1538, .D]
          (o₁.push r' (.G n))
        rw [hpush r' (.G n)] at hfold
        exact congrArg some hfold
    | D | C | P => simp [mapPop, hp]

theorem unx_map_post {R S A B : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (r : R)
    (g : R → A) (g' : S → B) (h : A → B) (hg : ∀ x, h (g x) = g' (f x)) :
    (unx o₁ r).map (h ∘ g) = (unx o₂ (f r)).map g' := by
  calc
    (unx o₁ r).map (h ∘ g) = (unx o₁ r).map (g' ∘ f) := by
      congr 1
      funext x
      exact hg x
    _ = ((unx o₁ r).map f).map g' := by
      cases hu : unx o₁ r <;> simp [hu, Function.comp_def]
    _ = (unx o₂ (f r)).map g' := by
      exact congrArg (Option.map g') (unx_map o₁ o₂ f hpop hpush r)

theorem rEnd_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (c : St R) :
    (rEnd o₁ c).map (mapSt f) = rEnd o₂ (mapSt f c) := by
  cases c with
  | mk d l r =>
    cases l with
    | nil => rfl
    | cons s l =>
      cases s with
      | x n => cases n <;> simp [rEnd, mapSt, lx, hpush]
      | _ => simp [rEnd, mapSt, lx, hpush]

theorem rC_map {R S : Type} (f : R → S)
    (l : List LS) (r : R) : (rC l r).map (mapSt f) = rC l (f r) := by
  cases l with
  | nil => rfl
  | cons s l =>
    cases s with
    | x n => cases n <;> simp [rC, mapSt, lx]
    | _ => simp [rC, mapSt, lx]

theorem rPD3_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (l : List LS)
    (p : Option (RI × R)) :
    (rPD3 o₁ l p).map (mapSt f) = rPD3 o₂ l (mapPop f p) := by
  cases p with
  | none => rfl
  | some p =>
    obtain ⟨i, r⟩ := p
    cases i with
    | x n => cases n <;> simp [rPD3, mapPop, mapSt, hpush]
    | D =>
      simpa [rPD3, mapPop, mapSt] using
        (unx_map_post o₁ o₂ f hpop hpush r
          (fun x => (⟨true, .D :: .C1 :: .C2 :: l, x⟩ : St R))
          (fun x => (⟨true, .D :: .C1 :: .C2 :: l, x⟩ : St S)) (mapSt f) (by intro; rfl))
    | C =>
      simpa [rPD3, mapPop, mapSt] using
        (unx_map_post o₁ o₂ f hpop hpush r
          (fun x => (⟨true, .D :: .G1 :: l, o₁.push x .P⟩ : St R))
          (fun x => (⟨true, .D :: .G1 :: l, o₂.push x .P⟩ : St S))
          (mapSt f) (by intro; simp [mapSt, hpush]))
    | P => simp [rPD3, mapPop, mapSt]
    | G n => simp [rPD3, mapPop, mapSt, hpush]

theorem rP2_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (c : St R)
    (p : Option (RI × R)) :
    (rP2 o₁ c p).map (mapSt f) = rP2 o₂ (mapSt f c) (mapPop f p) := by
  cases p with
  | none => rfl
  | some p =>
    obtain ⟨i, r⟩ := p
    cases i with
    | x n => simp [rP2, mapPop, mapSt, hpush]
    | D =>
      simp only [rP2, mapPop, Option.map_some]
      rw [← hpop r]
      exact rPD3_map o₁ o₂ f hpop hpush c.l (o₁.pop r)
    | C =>
      simpa [rP2, mapPop, mapSt] using
        (unx_map_post o₁ o₂ f hpop hpush r
          (fun x => (⟨false, c.l, o₁.push (o₁.push (o₁.push x .P) .D) .P⟩ : St R))
          (fun x => (⟨false, c.l, o₂.push (o₂.push (o₂.push x .P) .D) .P⟩ : St S))
          (mapSt f) (by intro; simp [mapSt, hpush]))
    | P => simp [rP2, mapPop, mapSt, hpush]
    | G n => simp [rP2, mapPop, mapSt]

theorem rItem_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (c : St R)
    (p : Option (RI × R)) :
    (rItem o₁ c p).map (mapSt f) = rItem o₂ (mapSt f c) (mapPop f p) := by
  cases p with
  | none => exact rEnd_map o₁ o₂ f hpush c
  | some p =>
    obtain ⟨i, r⟩ := p
    cases i with
    | x n => simp [rItem, mapPop, mapSt, hpush]
    | D => simp [rItem, mapPop, mapSt]
    | C => exact rC_map f c.l r
    | P =>
      simp only [rItem, mapPop, Option.map_some]
      rw [← hpop r]
      exact rP2_map o₁ o₂ f hpop hpush c (o₁.pop r)
    | G n => simp [rItem, mapPop, mapSt]

theorem lEmpty_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (r : R)
    (p : Option (RI × R)) :
    (lEmpty o₁ r p).map (mapSt f) = lEmpty o₂ (f r) (mapPop f p) := by
  cases p with
  | none => rfl
  | some p =>
    obtain ⟨i, r'⟩ := p
    cases i with
    | x n => rfl
    | D => rfl
    | C =>
      simpa [lEmpty, mapPop, mapSt] using
        (unx_map_post o₁ o₂ f hpop hpush r'
          (fun x => (⟨true, [.D, .C1], o₁.push x .P⟩ : St R))
          (fun x => (⟨true, [.D, .C1], o₂.push x .P⟩ : St S))
          (mapSt f) (by intro; simp [mapSt, hpush]))
    | P => rfl
    | G n => rfl

theorem lSym_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (r : R)
    (l : List LS) (s : LS) :
    (lSym o₁ r l s).map (mapSt f) = lSym o₂ (f r) l s := by
  cases s with
  | F3 =>
    cases l with
    | nil => simp [lSym, lF3, mapSt]
    | cons s l =>
      cases s with
      | x n => cases n <;> simp [lSym, lF3, mapSt]
      | _ => simp [lSym, lF3, mapSt]
  | _ => simp [lSym, lF3, mapSt, hpush]

theorem lStep_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (r : R) (l : List LS) :
    (lStep o₁ r l).map (mapSt f) = lStep o₂ (f r) l := by
  cases l with
  | nil =>
    simp only [lStep]
    rw [← hpop r]
    exact lEmpty_map o₁ o₂ f hpop hpush r (o₁.pop r)
  | cons s l => exact lSym_map o₁ o₂ f hpush r l s

theorem simple_map {R S : Type} (o₁ : ROps R) (o₂ : ROps S) (f : R → S)
    (hpop : ∀ r, mapPop f (o₁.pop r) = o₂.pop (f r))
    (hpush : ∀ r i, f (o₁.push r i) = o₂.push (f r) i) (c : St R) :
    (F.simple o₁ c).map (mapSt f) = F.simple o₂ (mapSt f c) := by
  obtain ⟨d, l, r⟩ := c
  cases d
  · simp only [F.simple]
    exact lStep_map o₁ o₂ f hpop hpush r l
  · simp only [F.simple]
    change (rItem o₁ ⟨true, l, r⟩ (o₁.pop r)).map (mapSt f) =
      rItem o₂ ⟨true, l, f r⟩ (o₂.pop (f r))
    rw [← hpop r]
    exact rItem_map o₁ o₂ f hpop hpush ⟨true, l, r⟩ (o₁.pop r)

end Sk1.F
