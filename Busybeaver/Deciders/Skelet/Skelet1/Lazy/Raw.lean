import Busybeaver.Deciders.Skelet.Skelet1.Lazy.PushPop

/-!
# An unmerged view of the lazy tape

The ordinary denotation merges adjacent `G` blocks.  The simulator sometimes
needs to inspect those blocks one at a time, so this view preserves the
representation's separators while still describing the same physical tape.
-/

namespace Sk1

def Seg.itemsRawAux : List (Nat × Sep) → Nat → List RI → List RI
  | [], tr, t => if tr = 0 then t else .x tr :: t
  | (a, sp) :: rest, tr, t =>
      (if a = 0 then [] else [.x a]) ++ [sp.item] ++ itemsRawAux rest tr t

def Seg.itemsRaw (g : Seg) (t : List RI) : List RI := itemsRawAux g.segs g.trail t

def flatBelowRaw (termP : Bool) : List Seg → List RI
  | [] => if termP then [.P] else []
  | g :: gs => .C :: g.itemsRaw (flatBelowRaw termP gs)

def RT.denRaw (t : RT) : Option (List RI) :=
  (matBelow t.termP 0 0 t.below).map fun gs => t.top.itemsRaw (flatBelowRaw t.termP gs)

/-- Eager tape contents that are currently visible through the deferred levels.
If a level cannot yet be materialized, the view stops immediately before it. -/
def viewBelow : Bool → Nat → Nat → List LBlk → List RI
  | termP, _, _, [] => if termP then [.P] else []
  | termP, s, r, b :: bs =>
      let s' := b.s + s
      let r' := max b.r (b.s + r)
      match b.body.apply s' r' bs.isEmpty termP with
      | none => []
      | some g => .C :: g.itemsRaw (viewBelow termP (4 * s') (4 * r') bs)

def RT.view (t : RT) : List RI := t.top.itemsRaw (viewBelow t.termP 0 0 t.below)

def NoHeadX (xs : List RI) : Prop := ∀ n ys, xs ≠ .x n :: ys
def NoHeadG (xs : List RI) : Prop := ∀ n ys, xs ≠ .G n :: ys

theorem flatBelowRaw_noHeadX (termP : Bool) (gs : List Seg) : NoHeadX (flatBelowRaw termP gs) := by
  cases gs with
  | nil => cases termP <;> simp [flatBelowRaw, NoHeadX]
  | cons g gs => simp [flatBelowRaw, NoHeadX]

theorem flatBelowRaw_noHeadG (termP : Bool) (gs : List Seg) : NoHeadG (flatBelowRaw termP gs) := by
  cases gs with
  | nil => cases termP <;> simp [flatBelowRaw, NoHeadG]
  | cons g gs => simp [flatBelowRaw, NoHeadG]

theorem viewBelow_noHeadX (termP : Bool) (s r : Nat) (bs : List LBlk) :
    NoHeadX (viewBelow termP s r bs) := by
  cases bs with
  | nil => cases termP <;> simp [viewBelow, NoHeadX]
  | cons b bs =>
    cases h : b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty termP <;>
      simp [viewBelow, h, NoHeadX]

theorem viewBelow_noHeadG (termP : Bool) (s r : Nat) (bs : List LBlk) :
    NoHeadG (viewBelow termP s r bs) := by
  cases bs with
  | nil => cases termP <;> simp [viewBelow, NoHeadG]
  | cons b bs =>
    cases h : b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty termP <;>
      simp [viewBelow, h, NoHeadG]

theorem viewBelow_addPend (termP : Bool) (s r : Nat) (bs : List LBlk)
    (h1 : s ≤ r) (h2 : s = 0 → r = 0) :
    viewBelow termP 0 0 (addPend s r bs) = viewBelow termP s r bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    have hs : b.s + s ≤ max b.r (b.s + r) := by omega
    simp only [addPend, viewBelow, Nat.add_zero]
    rw [show max (max b.r (b.s + r)) (b.s + s) = max b.r (b.s + r) by
      exact max_eq_left hs]

theorem Seg.itemsRaw_pushX (g : Seg) (n : Nat) (t : List RI) (ht : NoHeadX t) :
    (g.pushX n).itemsRaw t = Sk1.pushX n (g.itemsRaw t) := by
  obtain ⟨segs, tr⟩ := g
  cases n with
  | zero => simp [Seg.pushX, Seg.itemsRaw, Sk1.pushX]
  | succ n =>
    cases segs with
    | nil =>
      cases tr with
      | zero =>
        cases t with
        | nil => simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
        | cons i xs =>
          cases i with
          | x m => exact False.elim (ht m xs rfl)
          | D => simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
          | C => simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
          | P => simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
          | G m => simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
      | succ tr =>
        simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX]
        omega
    | cons p rest =>
      cases p with
      | mk a sp =>
        cases a with
        | zero => cases sp <;> simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX, Sep.item]
        | succ a =>
          simp [Seg.pushX, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushX, Sep.item]
          omega

theorem Seg.itemsRaw_pushG (g : Seg) (n : Nat) (t : List RI) (ht : NoHeadG t) :
    (g.pushG n).itemsRaw t = Sk1.pushG n (g.itemsRaw t) := by
  obtain ⟨segs, tr⟩ := g
  cases n with
  | zero => simp [Seg.pushG, Seg.itemsRaw, Sk1.pushG]
  | succ n =>
    cases segs with
    | nil =>
      cases tr with
      | zero =>
        cases t with
        | nil => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
        | cons i xs =>
          cases i with
          | x m => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
          | D => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
          | C => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
          | P => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
          | G m => exact False.elim (ht m xs rfl)
      | succ tr => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
    | cons p rest =>
      cases p with
      | mk a sp =>
        cases a with
        | succ a => simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
        | zero =>
          cases sp <;> simp [Seg.pushG, Seg.itemsRaw, Seg.itemsRawAux, Sk1.pushG, Sep.item]
  all_goals rfl

theorem Seg.itemsRaw_prepend (g : Seg) (sp : Sep) (t : List RI) :
    ({ g with segs := (0, sp) :: g.segs }).itemsRaw t = sp.item :: g.itemsRaw t := by
  cases g with
  | mk segs tr => simp [Seg.itemsRaw, Seg.itemsRawAux]

theorem RT.view_push (t : RT) (i : RI) : RT.view (t.push i) = ePush (RT.view t) i := by
  obtain ⟨top, below, termP⟩ := t
  cases i with
  | x n =>
    simp only [RT.push, RT.view]
    rw [Seg.itemsRaw_pushX _ _ _ (viewBelow_noHeadX termP 0 0 below)]
    rfl
  | G n =>
    simp only [RT.push, RT.view]
    rw [Seg.itemsRaw_pushG _ _ _ (viewBelow_noHeadG termP 0 0 below)]
    rfl
  | D =>
    simp only [RT.push, RT.view, Seg.itemsRaw_prepend]
    rfl
  | P =>
    simp only [RT.push]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hTop, hBelow⟩, hterm⟩ := h
      obtain ⟨topSegs, topTrail⟩ := top
      simp only [Seg.isEmpty, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hTop
      rcases hTop with ⟨rfl, rfl⟩
      simp only [List.isEmpty_iff] at hBelow
      subst below
      simp [RT.view, viewBelow, Seg.itemsRaw, Seg.itemsRawAux, Sep.item, ePush, hterm]
    · simp [RT.view, Seg.itemsRaw_prepend, Sep.item, ePush]
  | C =>
    simp [RT.push, RT.view, viewBelow, Seg.itemsRaw, Seg.itemsRawAux, Seg.apply, ePush]

theorem RT.view_pop (t : RT) (hinv : t.Inv) :
    (t.pop).map (fun p => (p.1, RT.view p.2)) = eagerOps.pop (RT.view t) := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hTopInv, hBelowInv⟩ := hinv
  cases hs : top.segs with
  | cons p rest =>
    cases p with
    | mk a sp =>
      cases a with
      | zero => simp [RT.pop, RT.view, Seg.itemsRaw, Seg.itemsRawAux, eagerOps, hs]
      | succ a => simp [RT.pop, RT.view, Seg.itemsRaw, Seg.itemsRawAux, eagerOps, hs]
  | nil =>
    by_cases htr : top.trail = 0
    · cases hb : below with
      | nil =>
        cases termP <;>
          simp [RT.pop, RT.view, viewBelow, Seg.itemsRaw, Seg.itemsRawAux, eagerOps,
            hs, htr, hb]
      | cons b bs =>
        have hbi := hBelowInv b (by simp [hb])
        obtain ⟨hbnz, hble, hbzero⟩ := hbi
        have hmax : max b.r b.s = b.r := max_eq_left hble
        cases ha : b.body.apply b.s b.r bs.isEmpty termP with
        | none =>
          simp [RT.pop, RT.view, viewBelow, Seg.itemsRaw, Seg.itemsRawAux, eagerOps,
            hs, htr, hb, ha, hmax]
        | some g =>
          have hcomp := viewBelow_addPend termP (4 * b.s) (4 * b.r) bs
            (by omega) (by intro hz; have := hbzero (by omega); omega)
          simp only [RT.pop, hs, htr, if_pos, hb, ha, Option.map_some]
          simp only [RT.view, viewBelow, hs, htr, hb, ha, hmax, Nat.add_zero]
          rw [hcomp]
          simp [eagerOps, Seg.itemsRaw, Seg.itemsRawAux, hs, htr]
    · simp [RT.pop, RT.view, viewBelow, Seg.itemsRaw, Seg.itemsRawAux, eagerOps,
        hs, htr]

/-- A segment list has no stored `G` separator immediately followed by another
`G` separator without an intervening `x` run. -/
def Sep.isG : Sep → Bool
  | .G _ => true
  | _ => false

def Seg.NoGG : List (Nat × Sep) → Prop
  | [] => True
  | [_] => True
  | (_, sp) :: (b, sp') :: rest =>
      (Sep.isG sp = true → b = 0 → Sep.isG sp' = true → False) ∧ NoGG ((b, sp') :: rest)

def Seg.Clean (g : Seg) : Prop := Seg.NoGG g.segs

def RT.Clean (t : RT) : Prop := t.top.Clean ∧ ∀ b ∈ t.below, b.body.Clean

def RT.Good (t : RT) : Prop := t.Inv ∧ t.Clean

theorem Seg.noGG_tail {p : Nat × Sep} {ps : List (Nat × Sep)}
    (h : Seg.NoGG (p :: ps)) : Seg.NoGG ps := by
  cases ps with
  | nil => trivial
  | cons q qs => exact h.2

theorem Seg.itemsRawAux_tail_noHeadG {p : Nat × Sep} {ps : List (Nat × Sep)}
    (tr : Nat) (t : List RI) (hclean : Seg.NoGG (p :: ps))
    (ht : NoHeadG (if tr = 0 then t else .x tr :: t))
    (hg : Sep.isG p.2 = true) :
    NoHeadG (Seg.itemsRawAux ps tr t) := by
  cases ps with
  | nil =>
    cases tr with
    | zero => simpa [Seg.itemsRawAux] using ht
    | succ n => simp [Seg.itemsRawAux, NoHeadG]
  | cons q qs =>
    obtain ⟨b, sp⟩ := q
    cases b with
    | zero =>
      cases sp with
      | D => simp [Seg.itemsRawAux, NoHeadG, Sep.item]
      | P => simp [Seg.itemsRawAux, NoHeadG, Sep.item]
      | G n =>
        have hpair := hclean.1 hg rfl (by rfl)
        cases hpair
    | succ b => simp [Seg.itemsRawAux, NoHeadG]

theorem Seg.itemsRaw_eq_items (g : Seg) (t : List RI) (hc : g.Clean)
    (hnz : g.NZ) (htx : NoHeadX t) (htg : NoHeadG t) : g.itemsRaw t = g.items t := by
  obtain ⟨segs, tr⟩ := g
  change Seg.NoGG segs at hc
  change ∀ p ∈ segs, p.2 ≠ Sep.G 0 at hnz
  induction segs with
  | nil =>
    change Seg.itemsRawAux [] tr t = Sk1.pushX tr t
    cases htr : tr with
    | zero => simp [Seg.itemsRawAux, Sk1.pushX, htr]
    | succ n =>
      cases ht : t with
      | nil => simp [Seg.itemsRawAux, Sk1.pushX, htr, ht]
      | cons i tail =>
        cases i with
        | x m => exact False.elim (htx m tail ht)
        | _ => simp [Seg.itemsRawAux, Sk1.pushX, htr, ht, pushX]
  | cons p ps ih =>
    obtain ⟨a, sp⟩ := p
    have hclean : Seg.NoGG ((a, sp) :: ps) := hc
    have htailClean : Seg.NoGG ps := Seg.noGG_tail hclean
    have htailNZ : ∀ q ∈ ps, q.2 ≠ Sep.G 0 := by
      intro q hq
      exact hnz q (List.mem_cons_of_mem _ hq)
    have htailEq : Seg.itemsRaw ⟨ps, tr⟩ t = Seg.items ⟨ps, tr⟩ t :=
      ih htailClean htailNZ
    change Seg.itemsRawAux ps tr t = Seg.items ⟨ps, tr⟩ t at htailEq
    change Seg.itemsRawAux ((a, sp) :: ps) tr t =
      Sk1.pushX a (sp.push (Seg.items ⟨ps, tr⟩ t))
    rw [Seg.itemsRawAux, htailEq]
    have hbase : NoHeadG (if tr = 0 then t else .x tr :: t) := by
      by_cases htr : tr = 0
      · simpa [htr] using htg
      · simp [htr, NoHeadG]
    have htailRawG : Sep.isG sp = true → NoHeadG (Seg.itemsRawAux ps tr t) := by
      intro hg
      exact Seg.itemsRawAux_tail_noHeadG tr t hclean hbase hg
    have htailG : Sep.isG sp = true → NoHeadG (Seg.items ⟨ps, tr⟩ t) := by
      intro hg
      rw [← htailEq]
      exact htailRawG hg
    have hpushG : ∀ n, n ≠ 0 → Sep.isG sp = true → Sk1.pushG n (Seg.items ⟨ps, tr⟩ t) =
        .G n :: Seg.items ⟨ps, tr⟩ t := by
      intro n hn hsp
      cases htail : Seg.items ⟨ps, tr⟩ t with
      | nil => simp [Sk1.pushG, hn]
      | cons i rest =>
        cases i with
        | G m => exact False.elim (htailG hsp m rest htail)
        | _ => simp [Sk1.pushG, hn]
    by_cases ha : a = 0
    · subst a
      cases sp with
      | D => simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX]
      | P => simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX]
      | G n =>
        have hn : n ≠ 0 := by
          intro hz
          have hneq := hnz (0, Sep.G n) (by simp)
          apply hneq
          simp [hz]
        have hpG := hpushG n hn rfl
        simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX, hn, hpG]
    · cases a with
      | zero => contradiction
      | succ n =>
        cases sp with
        | D => simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX]
        | P => simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX]
        | G m =>
          have hm : m ≠ 0 := by
            intro hz
            have hneq := hnz (Nat.succ n, Sep.G m) (by simp)
            apply hneq
            simp [hz]
          have hpG := hpushG m hm rfl
          simp [Seg.itemsRawAux, Sep.item, Sep.push, Sk1.pushX, pushX, hm, hpG]

theorem viewBelow_eq_flatBelowRaw (termP : Bool) (s r : Nat) (bs : List LBlk)
    (gs : List Seg) (h : matBelow termP s r bs = some gs) :
    viewBelow termP s r bs = flatBelowRaw termP gs := by
  induction bs generalizing s r gs with
  | nil => simp [matBelow] at h; subst gs; simp [viewBelow, flatBelowRaw]
  | cons b bs ih =>
    rw [matBelow_cons] at h
    simp only [viewBelow]
    cases ha : b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty termP with
    | none => simp [ha] at h
    | some g =>
      simp only [ha, Option.bind_some] at h
      cases hm : matBelow termP (4 * (b.s + s)) (4 * max b.r (b.s + r)) bs with
      | none => simp [hm] at h
      | some tail =>
        simp only [hm, Option.map_some, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have htail := ih (s := 4 * (b.s + s)) (r := 4 * max b.r (b.s + r))
          (gs := tail) hm
        simp [ha, htail, flatBelowRaw]

theorem flatBelowRaw_eq_flatBelow (termP : Bool) (gs : List Seg)
    (hc : ∀ g ∈ gs, g.Clean) (hnz : ∀ g ∈ gs, g.NZ) :
    flatBelowRaw termP gs = flatBelow termP gs := by
  induction gs with
  | nil => simp [flatBelowRaw, flatBelow]
  | cons g gs ih =>
    have htailC : ∀ b ∈ gs, b.Clean := fun b hb => hc b (List.mem_cons_of_mem _ hb)
    have htailN : ∀ b ∈ gs, b.NZ := fun b hb => hnz b (List.mem_cons_of_mem _ hb)
    have htail := ih htailC htailN
    have hNoX : NoHeadX (flatBelow termP gs) := by
      cases gs <;> cases termP <;> simp [flatBelow, NoHeadX]
    have hNoG : NoHeadG (flatBelow termP gs) := by
      cases gs <;> cases termP <;> simp [flatBelow, NoHeadG]
    simp only [flatBelowRaw, flatBelow, htail]
    exact congrArg (fun x => RI.C :: x) (Seg.itemsRaw_eq_items g _ (hc g (by simp))
      (hnz g (by simp)) hNoX hNoG)

theorem Seg.noGG_pushX (g : Seg) (n : Nat) (h : g.Clean) : (g.pushX n).Clean := by
  cases g with
  | mk segs tr =>
    cases n with
    | zero => simpa [Seg.pushX, Seg.Clean] using h
    | succ n =>
      cases segs with
      | nil => simp [Seg.Clean, Seg.pushX, Seg.NoGG]
      | cons p rest =>
        cases p with
        | mk a sp =>
          cases rest with
          | nil => simp [Seg.Clean, Seg.pushX, Seg.NoGG]
          | cons q qs =>
            cases q with
            | mk b sp' =>
              simp [Seg.Clean, Seg.pushX, Seg.NoGG] at h ⊢
              exact h

theorem Seg.noGG_pushG (g : Seg) (n : Nat) (h : g.Clean) : (g.pushG n).Clean := by
  cases g with
  | mk segs tr =>
    change Seg.NoGG segs at h
    by_cases hn : n = 0
    · simp [Seg.pushG, hn, Seg.Clean, h]
    · cases segs with
      | nil => simp [Seg.pushG, hn, Seg.Clean, Seg.NoGG]
      | cons p rest =>
        cases p with
        | mk a sp =>
          cases a with
          | succ a =>
            simpa [Seg.pushG, hn, Seg.Clean, Seg.NoGG] using h
          | zero =>
            cases sp with
            | D =>
                simp [Seg.pushG, hn, Seg.Clean, Seg.NoGG, Sep.isG] at h ⊢
                exact h
            | P =>
                simp [Seg.pushG, hn, Seg.Clean, Seg.NoGG, Sep.isG] at h ⊢
                exact h
            | G m =>
              simp only [Seg.pushG, hn, if_false, Seg.Clean]
              cases rest with
              | nil => trivial
              | cons q qs =>
                cases q with
                | mk b sp' =>
                  simp only [Seg.NoGG] at h ⊢
                  rcases h with ⟨hpair, htail⟩
                  refine ⟨?_, htail⟩
                  intro hk hb hj
                  exact hpair rfl hb hj

theorem Seg.noGG_apply {s r : Nat} {last termP : Bool} {g g' : Seg}
    (h : g.apply s r last termP = some g') (hc : g.Clean) : g'.Clean := by
  obtain ⟨segs, tr⟩ := g
  cases segs with
  | nil =>
    simp only [Seg.apply] at h
    split_ifs at h <;> cases h <;> simp [Seg.Clean, Seg.NoGG]
  | cons p rest =>
    cases p with
    | mk a sp =>
      cases rest with
      | nil =>
        simp only [Seg.apply] at h
        split_ifs at h <;> cases h <;> simp [Seg.Clean, Seg.NoGG]
      | cons q qs =>
        cases q with
        | mk b sp' =>
          simp only [Seg.apply] at h
          split_ifs at h <;> cases h <;>
            simpa [Seg.Clean, Seg.NoGG] using hc

theorem matBelow_clean (termP : Bool) (s r : Nat) (bs : List LBlk)
    (hclean : ∀ b ∈ bs, b.body.Clean) {gs : List Seg}
    (h : matBelow termP s r bs = some gs) : ∀ g ∈ gs, g.Clean := by
  induction bs generalizing s r gs with
  | nil => simp [matBelow] at h; subst gs; simp
  | cons b bs ih =>
    rw [matBelow_cons] at h
    cases ha : b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty termP with
    | none => simp [ha] at h
    | some g =>
      cases hm : matBelow termP (4 * (b.s + s)) (4 * max b.r (b.s + r)) bs with
      | none => simp [ha, hm] at h
      | some tail =>
        simp only [ha, Option.bind_some, hm, Option.map_some, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact Seg.noGG_apply ha (hclean b (by simp))
        · exact ih (s := 4 * (b.s + s)) (r := 4 * max b.r (b.s + r))
            (fun c hc => hclean c (List.mem_cons_of_mem _ hc)) hm g' hg'

theorem matBelow_NZ (termP : Bool) (s r : Nat) (bs : List LBlk)
    (hinv : ∀ b ∈ bs, b.Inv) {gs : List Seg}
    (h : matBelow termP s r bs = some gs) : ∀ g ∈ gs, g.NZ := by
  induction bs generalizing s r gs with
  | nil => simp [matBelow] at h; subst gs; simp
  | cons b bs ih =>
    rw [matBelow_cons] at h
    cases ha : b.body.apply (b.s + s) (max b.r (b.s + r)) bs.isEmpty termP with
    | none => simp [ha] at h
    | some g =>
      cases hm : matBelow termP (4 * (b.s + s)) (4 * max b.r (b.s + r)) bs with
      | none => simp [ha, hm] at h
      | some tail =>
        simp only [ha, Option.bind_some, hm, Option.map_some, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro g' hg'
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact seg_apply_NZ _ _ _ _ _ _ (hinv b (by simp)).1 ha
        · exact ih (s := 4 * (b.s + s)) (r := 4 * max b.r (b.s + r))
            (fun c hc => hinv c (List.mem_cons_of_mem _ hc)) hm g' hg'

theorem RT.view_eq_den {t : RT} (hgood : t.Good) {L : List RI} (hden : t.den = some L) :
    t.view = L := by
  obtain ⟨hinv, hclean⟩ := hgood
  obtain ⟨htopNZ, hbelowInv⟩ := hinv
  obtain ⟨htopClean, hbelowClean⟩ := hclean
  simp only [RT.den, Option.map_eq_some_iff] at hden
  obtain ⟨gs, hmat, hL⟩ := hden
  subst L
  have hv := viewBelow_eq_flatBelowRaw t.termP 0 0 t.below gs hmat
  have hgsClean := matBelow_clean t.termP 0 0 t.below hbelowClean hmat
  have hgsNZ := matBelow_NZ t.termP 0 0 t.below hbelowInv hmat
  have hflat := flatBelowRaw_eq_flatBelow t.termP gs hgsClean hgsNZ
  have htailX : NoHeadX (flatBelow t.termP gs) := by
    cases gs <;> cases t.termP <;> simp [flatBelow, NoHeadX]
  have htailG : NoHeadG (flatBelow t.termP gs) := by
    cases gs <;> cases t.termP <;> simp [flatBelow, NoHeadG]
  rw [RT.view, hv, hflat]
  exact Seg.itemsRaw_eq_items t.top _ htopClean htopNZ htailX htailG

theorem Seg.noGG_prepend {sp : Sep} {g : Seg} (hsp : Sep.isG sp = false)
    (hg : g.Clean) : ({ g with segs := (0, sp) :: g.segs }).Clean := by
  cases g with
  | mk segs tr =>
    cases segs with
    | nil => simp [Seg.Clean, Seg.NoGG]
    | cons p rest =>
      cases p with
      | mk b sp' =>
        simp only [Seg.Clean, Seg.NoGG] at hg ⊢
        refine ⟨?_, hg⟩
        intro hG hb hG'
        simp [hsp] at hG

theorem addPend_clean (s r : Nat) (bs : List LBlk)
    (h : ∀ b ∈ bs, b.body.Clean) : ∀ b ∈ addPend s r bs, b.body.Clean := by
  cases bs with
  | nil => simp [addPend]
  | cons b bs =>
    intro c hc
    simp only [addPend, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h b (List.mem_cons_self ..)
    · exact h c (List.mem_cons_of_mem _ hc)

theorem RT.push_clean (t : RT) (hc : t.Clean) (i : RI) : (t.push i).Clean := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hTop, hBelow⟩ := hc
  cases i with
  | x n => simpa [RT.push] using ⟨Seg.noGG_pushX top n hTop, hBelow⟩
  | G n => simpa [RT.push] using ⟨Seg.noGG_pushG top n hTop, hBelow⟩
  | D => simpa [RT.push] using ⟨Seg.noGG_prepend (by rfl) hTop, hBelow⟩
  | P =>
      simp only [RT.push]
      split
      · exact ⟨hTop, hBelow⟩
      · exact ⟨Seg.noGG_prepend (by rfl) hTop, hBelow⟩
  | C =>
      simp only [RT.push]
      refine ⟨by simp [Seg.Clean, Seg.NoGG], ?_⟩
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hTop
      · exact hBelow b hb

theorem RT.pop_clean (t t' : RT) (i : RI) (hc : t.Clean)
    (h : t.pop = some (i, t')) : t'.Clean := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hTop, hBelow⟩ := hc
  simp only [RT.pop] at h
  cases hs : top.segs with
  | cons p rest =>
    simp only [hs] at h
    cases p with
    | mk a sp =>
      by_cases ha : a = 0
      · simp only [ha, if_pos] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hBelow⟩
        change Seg.NoGG rest
        apply Seg.noGG_tail
        simpa [Seg.Clean, hs] using hTop
      · simp only [ha, if_false] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hBelow⟩
        change Seg.NoGG ((0, sp) :: rest)
        have hsrc : Seg.NoGG ((a, sp) :: rest) := by simpa [Seg.Clean, hs] using hTop
        cases rest with
        | nil => trivial
        | cons q qs =>
          cases q with
          | mk b sp' =>
            simpa [Seg.NoGG] using hsrc
  | nil =>
    simp only [hs] at h
    by_cases htr : top.trail = 0
    · simp only [htr, if_pos] at h
      cases hb : below with
      | nil =>
        simp only [hb] at h
        cases termP with
        | false => simp at h
        | true =>
          simp only [Bool.not_false, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hTop, by simp⟩
      | cons b bs =>
        simp only [hb] at h
        cases ha : b.body.apply b.s b.r bs.isEmpty termP with
        | none => simp [ha] at h
        | some g =>
          simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨Seg.noGG_apply ha (hBelow b (by simp [hb])), ?_⟩
          apply addPend_clean
          intro c hc'
          exact hBelow c (by simp [hb, hc'])
    · simp only [htr, if_false] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp [Seg.Clean, Seg.NoGG], hBelow⟩

theorem RT.tick_clean (t t' : RT) (hc : t.Clean) (h : t.tick = some t') : t'.Clean := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hTop, hBelow⟩ := hc
  cases termP with
  | false => simp [RT.tick] at h
  | true =>
    by_cases hp : top.hasP
    · simp [RT.tick, hp] at h
    · cases below with
      | nil =>
        simp [RT.tick, hp] at h
        cases h
        exact ⟨hTop, by simp⟩
      | cons b bs =>
        by_cases ht : 1 ≤ top.trail
        · simp [RT.tick, hp, ht] at h
          cases h
          refine ⟨hTop, ?_⟩
          intro c hc'
          simp only [List.mem_cons] at hc'
          rcases hc' with rfl | hc'
          · exact hBelow b (by simp)
          · exact hBelow c (by simp [hc'])
        · simp [RT.tick, hp, ht] at h

theorem RT.tickN_clean (t t' : RT) (m : Nat) (hc : t.Clean)
    (h : RT.tickN m t = some t') : t'.Clean := by
  obtain ⟨top, below, termP⟩ := t
  obtain ⟨hTop, hBelow⟩ := hc
  cases termP with
  | false => simp [RT.tickN] at h
  | true =>
    by_cases hp : top.hasP
    · simp [RT.tickN, hp] at h
    · cases below with
      | nil =>
        simp [RT.tickN, hp] at h
        cases h
        exact ⟨hTop, by simp⟩
      | cons b bs =>
        by_cases ht : m ≤ top.trail
        · simp [RT.tickN, hp, ht] at h
          cases h
          refine ⟨hTop, ?_⟩
          intro c hc'
          simp only [List.mem_cons] at hc'
          rcases hc' with rfl | hc'
          · exact hBelow b (by simp)
          · exact hBelow c (by simp [hc'])
        · simp [RT.tickN, hp, ht] at h

theorem RT.good_push (t : RT) (h : t.Good) (i : RI) : (t.push i).Good :=
  ⟨RT.push_inv t h.1 i, RT.push_clean t h.2 i⟩

theorem RT.good_pop (t t' : RT) (i : RI) (hgood : t.Good)
    (h : t.pop = some (i, t')) : t'.Good :=
  ⟨RT.pop_inv t t' i hgood.1 h, RT.pop_clean t t' i hgood.2 h⟩

theorem RT.good_tick (t t' : RT) (hgood : t.Good) (h : t.tick = some t') : t'.Good :=
  ⟨RT.tick_inv t t' hgood.1 h, RT.tick_clean t t' hgood.2 h⟩

theorem RT.good_tickN (t t' : RT) (m : Nat) (hm : 0 < m) (hgood : t.Good)
    (h : RT.tickN m t = some t') : t'.Good :=
  ⟨RT.tickN_inv t t' m hm hgood.1 h, RT.tickN_clean t t' m hgood.2 h⟩

theorem RT.ofList_clean (xs : List RI) : (RT.ofList xs).Clean := by
  induction xs with
  | nil => simp [RT.ofList, RT.Clean, Seg.Clean, Seg.NoGG]
  | cons i xs ih =>
    simp only [RT.ofList, List.foldr_cons]
    exact RT.push_clean _ ih i

theorem RT.ofList_good (xs : List RI) : (RT.ofList xs).Good :=
  ⟨RT.ofList_inv xs, RT.ofList_clean xs⟩

end Sk1
