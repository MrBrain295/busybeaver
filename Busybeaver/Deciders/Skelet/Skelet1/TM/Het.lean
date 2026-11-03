import Busybeaver.Deciders.Skelet.Skelet1.Cert.Steps
import Busybeaver.Deciders.Skelet.Skelet1.TM.SweepAlg

/-!
# A heterogeneous symbolic simulator

Counts are either pure numbers `k` or `M + k` for a universally quantified `M ≥ 1`.
The left tape is a visible list followed by an abstract tail, the right tape is a
visible list followed by an abstract tail that receives ticks as a deferred count.
Every operation fails (returns `none`) when it would need to look at an abstract
tail or to decide something that depends on `M`.
-/

namespace Sk1.Het

/-- A count: `k` (`h = false`) or `M + k` (`h = true`). -/
structure HN where
  h : Bool
  k : Nat
  deriving DecidableEq, Repr

def HN.den (M : Nat) (n : HN) : Nat := if n.h then M + n.k else n.k

def HN.pure (k : Nat) : HN := ⟨false, k⟩

def HN.isZero (n : HN) : Bool := !n.h && n.k == 0

def HN.add (a b : HN) : Option HN :=
  if a.h && b.h then none else some ⟨a.h || b.h, a.k + b.k⟩

def HN.pred (a : HN) : Option HN :=
  if a.k = 0 then none else some ⟨a.h, a.k - 1⟩

/-- Left symbols with heterogeneous `x` counts. -/
inductive HL
  | x (n : HN) | D | P | C0 | C1 | C2 | C3 | F0 | F1 | F2 | F3 | G0 | G1 | G2
  | Fs (n : Nat) | Gs (n : Nat) | Hs (n : Nat)
  deriving DecidableEq, Repr

def HL.den (M : Nat) : HL → LS
  | .x n => .x (n.den M)
  | .D => .D | .P => .P | .C0 => .C0 | .C1 => .C1 | .C2 => .C2 | .C3 => .C3
  | .F0 => .F0 | .F1 => .F1 | .F2 => .F2 | .F3 => .F3
  | .G0 => .G0 | .G1 => .G1 | .G2 => .G2
  | .Fs n => .Fs n | .Gs n => .Gs n | .Hs n => .Hs n

/-- Right items with heterogeneous `x` counts. -/
inductive HRI
  | x (n : HN) | D | C | P | G (n : Nat)
  deriving DecidableEq, Repr

def HRI.den (M : Nat) : HRI → RI
  | .x n => .x (n.den M)
  | .D => .D | .C => .C | .P => .P
  | .G n => .G n

structure HC where
  right : Bool
  l : List HL
  r : List HRI
  deriving DecidableEq, Repr

def HC.den (M : Nat) (T : List LS) (t : List RI) (c : HC) : St (List RI) :=
  ⟨c.right, c.l.map (HL.den M) ++ T, c.r.map (HRI.den M) ++ t⟩

/-! ## Operations -/

def hpushX (n : HN) (t : List HRI) : Option (List HRI) :=
  if n.isZero then some t else
  match t with
  | .x m :: t => (n.add m).map fun s => .x s :: t
  | [] => none
  | t => some (.x n :: t)

def hpushG (n : Nat) (t : List HRI) : Option (List HRI) :=
  if n = 0 then some t else
  match t with
  | .G m :: t => some (.G (n + m) :: t)
  | [] => none
  | t => some (.G n :: t)

def hpush (t : List HRI) (i : HRI) : Option (List HRI) :=
  match i with
  | .x n => hpushX n t
  | .G n => hpushG n t
  | i => some (i :: t)

def hlx (n : HN) (l : List HL) : Option (List HL) :=
  if n.isZero then some l else
  match l with
  | .x m :: l => (n.add m).map fun s => .x s :: l
  | [] => none
  | l => some (.x n :: l)

def hlG (n : Nat) (l : List HL) : Option (List HL) :=
  if n = 0 then some l else
  match l with
  | .Gs m :: l => some (.Gs (n + m) :: l)
  | [] => none
  | l => some (.Gs n :: l)

def hlH (n : Nat) (l : List HL) : Option (List HL) :=
  if n = 0 then some l else
  match l with
  | .Hs m :: l => some (.Hs (n + m) :: l)
  | [] => none
  | l => some (.Hs n :: l)

/-- The expansion of one `G` block (as pushed by `unx`). -/
def gExp : List HRI :=
  [.x (.pure 299), .D, .x (.pure 30826), .D, .x (.pure 72142), .D, .x (.pure 3076), .D,
    .x (.pure 1538), .D]

def hunx (t : List HRI) : Option (List HRI) :=
  match t with
  | .x n :: t => n.pred.bind fun n' => hpushX n' t
  | .G (n + 1) :: t => (hpushG n t).map fun t1 => gExp ++ t1
  | _ => none

/-- One simple step. -/
def hsimple (c : HC) : Option HC :=
  let l := c.l
  let r := c.r
  if c.right then
    match r with
    | [] => none
    | .x n :: r => (hlx n l).map fun l => ⟨true, l, r⟩
    | .D :: r => some ⟨true, .D :: l, r⟩
    | .C :: r =>
      match l with
      | .x n :: l => n.pred.bind fun n' => (hlx n' l).map fun l => ⟨true, .C0 :: l, r⟩
      | .D :: l => some ⟨true, .x (.pure 1) :: .P :: l, r⟩
      | .C0 :: l => some ⟨true, .G0 :: l, r⟩
      | .C2 :: l => some ⟨true, .F0 :: l, r⟩
      | _ => none
    | .P :: r1 =>
      match r1 with
      | [] => none
      | .x n :: r2 => (hlx n l).bind fun l => (hpush r2 .P).map fun r => ⟨true, l, r⟩
      | .D :: r2 =>
        match r2 with
        | .x n :: r3 => n.pred.bind fun n' => (hpushX n' r3).bind fun r4 =>
            (hpush r4 .P).map fun r5 => ⟨true, .D :: .C1 :: l, r5⟩
        | .D :: r3 => (hunx r3).map fun r4 => ⟨true, .D :: .C1 :: .C2 :: l, r4⟩
        | .C :: r3 => (hunx r3).bind fun r4 => (hpush r4 .P).map fun r5 => ⟨true, .D :: .G1 :: l, r5⟩
        | .P :: r3 => some ⟨true, .D :: .C1 :: l, r3⟩
        | .G n :: r3 => (hlH n l).bind fun l => (hpush r3 .D).bind fun r4 =>
            (hpush r4 .P).map fun r5 => ⟨true, l, r5⟩
        | [] => none
      | .C :: r2 => (hunx r2).bind fun r3 => (hpush r3 .P).bind fun r4 =>
          (hpush r4 .D).bind fun r5 => (hpush r5 .P).map fun r6 => ⟨false, l, r6⟩
      | .P :: r2 => (hlx (.pure 1) l).map fun l => ⟨true, l, r2⟩
      | .G _ :: _ => none
    | .G n :: r => (hlG n l).map fun l => ⟨true, l, r⟩
  else
    match l with
    | [] => none
    | .x n :: l => (hpush r (.x n)).map fun r => ⟨false, l, r⟩
    | .D :: l => (hpush r .D).map fun r => ⟨false, l, r⟩
    | .P :: l => (hpush r .P).map fun r => ⟨false, l, r⟩
    | .C0 :: l => some ⟨true, .x (.pure 1) :: .C1 :: l, r⟩
    | .C1 :: l => some ⟨true, .C2 :: l, r⟩
    | .C2 :: l => some ⟨true, .x (.pure 1) :: .C3 :: l, r⟩
    | .C3 :: l => (hpush r .C).map fun r => ⟨false, l, r⟩
    | .F0 :: l => some ⟨true, .x (.pure 1) :: .F1 :: l, r⟩
    | .F1 :: l => some ⟨true, .F2 :: l, r⟩
    | .F2 :: l => some ⟨true, .x (.pure 1) :: .F3 :: l, r⟩
    | .F3 :: .x n :: l => n.pred.bind fun n' => (hlx n' l).map fun l =>
        ⟨true, .D :: .C1 :: .P :: l, r⟩
    | .G0 :: l => some ⟨true, .x (.pure 1) :: .G1 :: l, r⟩
    | .G1 :: l => some ⟨true, .G2 :: l, r⟩
    | .G2 :: l => some ⟨true, .x (.pure 1) :: .D :: .P :: l, r⟩
    | .Gs n :: l => (hpush r (.G n)).map fun r => ⟨false, l, r⟩
    | _ => none

/-- Sweep of the visible part of the right tape: the new visible part and the
multiplier arriving at the abstract tail (with accumulated run `0`). -/
def hsweep : HN → Nat → List HRI → Option (List HRI × Nat)
  | a, n, [] => if a.isZero then some ([], n) else none
  | a, n, .x b :: t => (a.add b).bind fun a' => hsweep a' n t
  | a, n, .D :: t => (hsweep (.pure 0) n t).bind fun p => (hpushX a (.D :: p.1)).map (·, p.2)
  | a, n, .C :: t =>
      if n ≤ a.k then
        (hsweep (.pure 0) (4 * n) t).bind fun p => (hpushX (.pure (2 * n)) p.1).bind fun t1 =>
          (hpushX ⟨a.h, a.k - n⟩ (.C :: t1)).map (·, p.2)
      else none
  | a, n, .G g :: t => (hsweep (.pure 0) n t).bind fun p => (hpushG g p.1).bind fun t1 =>
      (hpushX a t1).map (·, p.2)
  | _, _, .P :: _ => none

def htick (c : HC) : Option (HC × Nat) :=
  if c.right then (hsweep (.pure 0) 1 c.r).map fun p => (⟨false, c.l, p.1⟩, p.2) else none

/-- One event: a tick if it succeeds, otherwise a simple step.  Returns the
multiplier deferred to the abstract right tail. -/
def hstep (c : HC) : Option (HC × Nat) :=
  match htick c with
  | some p => some p
  | none => (hsimple c).map (·, 0)

def hrun : Nat → HC → Option (HC × Nat)
  | 0, c => some (c, 0)
  | k + 1, c => (hstep c).bind fun p => (hrun k p.1).map fun q => (q.1, p.2 + q.2)

/-! ## Counts -/

section
variable {M : Nat}

@[simp] theorem HN.den_pure (k : Nat) : (HN.pure k).den M = k := rfl

@[simp] theorem HN.den_mk (h : Bool) (k : Nat) :
    (HN.mk h k).den M = if h then M + k else k := rfl

theorem HN.den_zero {n : HN} (hz : n.isZero = true) : n.den M = 0 := by
  obtain ⟨h, k⟩ := n
  cases h <;> simp_all [HN.isZero, HN.den]

theorem HN.den_ne_zero (hM : 1 ≤ M) {n : HN} (hz : n.isZero = false) : n.den M ≠ 0 := by
  obtain ⟨h, k⟩ := n
  cases h <;> simp_all [HN.isZero, HN.den]; omega

theorem HN.den_add {a b s : HN} (h : a.add b = some s) : s.den M = a.den M + b.den M := by
  obtain ⟨ha, ka⟩ := a
  obtain ⟨hb, kb⟩ := b
  unfold HN.add at h
  cases ha <;> cases hb <;> simp at h <;> subst h <;> simp [HN.den] <;> omega

theorem HN.den_pred {a b : HN} (h : a.pred = some b) : a.den M = b.den M + 1 := by
  obtain ⟨ha, ka⟩ := a
  unfold HN.pred at h
  split_ifs at h with hk
  cases h
  simp only at hk
  cases ha <;> simp [HN.den] <;> omega

end

/-! ## Soundness of the tape operations -/

section
variable {M : Nat}

@[simp] theorem HRI.den_x (n : HN) : (HRI.x n).den M = .x (n.den M) := rfl
@[simp] theorem HRI.den_D : HRI.D.den M = .D := rfl
@[simp] theorem HRI.den_C : HRI.C.den M = .C := rfl
@[simp] theorem HRI.den_P : HRI.P.den M = .P := rfl
@[simp] theorem HRI.den_G (n : Nat) : (HRI.G n).den M = .G n := rfl

theorem hpushX_den (hM : 1 ≤ M) {n : HN} {p p' : List HRI} (h : hpushX n p = some p')
    (t : List RI) : pushX (n.den M) (p.map (HRI.den M) ++ t) = p'.map (HRI.den M) ++ t := by
  unfold hpushX at h
  cases hz : n.isZero
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    have hne := HN.den_ne_zero hM hz
    rcases p with _ | ⟨i, p⟩
    · simp at h
    · cases i
      case x m =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨s, hs, rfl⟩ := h
        simp [pushX, hne, HN.den_add hs]
      all_goals (simp only [Option.some.injEq] at h; subst h; simp [pushX, hne])
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp [HN.den_zero hz, pushX_zero]

theorem hpushG_den {n : Nat} {p p' : List HRI} (h : hpushG n p = some p')
    (t : List RI) : pushG n (p.map (HRI.den M) ++ t) = p'.map (HRI.den M) ++ t := by
  unfold hpushG at h
  by_cases hz : n = 0
  · subst hz
    simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    simp [pushG]
  · simp only [hz, ↓reduceIte] at h
    rcases p with _ | ⟨i, p⟩
    · simp at h
    · cases i <;> (simp only [Option.some.injEq] at h; subst h; simp [pushG, hz])

theorem hpush_den (hM : 1 ≤ M) {i : HRI} {p p' : List HRI} (h : hpush p i = some p')
    (t : List RI) : ePush (p.map (HRI.den M) ++ t) (i.den M) = p'.map (HRI.den M) ++ t := by
  cases i
  case x n => exact hpushX_den hM h t
  case G n => exact hpushG_den h t
  all_goals (simp only [hpush, Option.some.injEq] at h; subst h; rfl)

@[simp] theorem HL.den_x (n : HN) : (HL.x n).den M = .x (n.den M) := rfl

theorem HL.den_ne_tl (s : HL) : s.den M ≠ .tl := by cases s <;> simp [HL.den]

theorem hlx_den (hM : 1 ≤ M) {n : HN} {l l' : List HL} (h : hlx n l = some l')
    (T : List LS) : lx (n.den M) (l.map (HL.den M) ++ T) = l'.map (HL.den M) ++ T := by
  unfold hlx at h
  cases hz : n.isZero
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
    have hne := HN.den_ne_zero hM hz
    rcases l with _ | ⟨i, l⟩
    · simp at h
    · cases i
      case x m =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨s, hs, rfl⟩ := h
        simp [lx, hne, HN.den_add hs]
      all_goals (simp only [Option.some.injEq] at h; subst h; simp [lx, hne, HL.den])
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp [HN.den_zero hz, lx]

theorem hlG_den {n : Nat} {l l' : List HL} (h : hlG n l = some l')
    (T : List LS) : lG n (l.map (HL.den M) ++ T) = l'.map (HL.den M) ++ T := by
  unfold hlG at h
  by_cases hz : n = 0
  · subst hz
    simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    simp [lG]
  · simp only [hz, ↓reduceIte] at h
    rcases l with _ | ⟨i, l⟩
    · simp at h
    · cases i <;> (simp only [Option.some.injEq] at h; subst h; simp [lG, hz, HL.den])

theorem hlH_den {n : Nat} {l l' : List HL} (h : hlH n l = some l')
    (T : List LS) : lH n (l.map (HL.den M) ++ T) = l'.map (HL.den M) ++ T := by
  unfold hlH at h
  by_cases hz : n = 0
  · subst hz
    simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    simp [lH]
  · simp only [hz, ↓reduceIte] at h
    rcases l with _ | ⟨i, l⟩
    · simp at h
    · cases i <;> (simp only [Option.some.injEq] at h; subst h; simp [lH, hz, HL.den])

theorem hunx_den (hM : 1 ≤ M) {p p' : List HRI} (h : hunx p = some p') (t : List RI) :
    unx eagerOps (p.map (HRI.den M) ++ t) = some (p'.map (HRI.den M) ++ t) := by
  unfold hunx at h
  split at h
  · rename_i n p
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨n', hn', hp⟩ := h
    have := HN.den_pred (M := M) hn'
    simp only [List.map_cons, HRI.den_x, List.cons_append, unx, eagerOps, this]
    simp [ePush, hpushX_den hM hp]
  · rename_i n p
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t1, ht1, rfl⟩ := h
    simp only [List.map_cons, HRI.den_G, List.cons_append, unx, eagerOps]
    simp [ePush, hpushG_den ht1, gExp, pushX]
  · cases h

@[local simp] theorem ePush_x (u : List RI) (n : Nat) : ePush u (.x n) = pushX n u := rfl
@[local simp] theorem ePush_G (u : List RI) (n : Nat) : ePush u (.G n) = pushG n u := rfl
@[local simp] theorem ePush_D (u : List RI) : ePush u .D = .D :: u := rfl
@[local simp] theorem ePush_C (u : List RI) : ePush u .C = .C :: u := rfl
@[local simp] theorem ePush_P (u : List RI) : ePush u .P = .P :: u := rfl

@[simp] theorem hpush_x (u : List HRI) (n : HN) : hpush u (.x n) = hpushX n u := rfl
@[simp] theorem hpush_G (u : List HRI) (n : Nat) : hpush u (.G n) = hpushG n u := rfl
@[simp] theorem hpush_D (u : List HRI) : hpush u .D = some (.D :: u) := rfl
@[simp] theorem hpush_C (u : List HRI) : hpush u .C = some (.C :: u) := rfl
@[simp] theorem hpush_P (u : List HRI) : hpush u .P = some (.P :: u) := rfl

@[local simp] theorem eagerOps_pop (u : List RI) : eagerOps.pop u =
    match u with | [] => none | i :: t => some (i, t) := rfl
@[local simp] theorem eagerOps_push (u : List RI) (i : RI) : eagerOps.push u i = ePush u i := rfl
@[local simp] theorem eagerOps_tick (u : List RI) : eagerOps.tick u = sweep 0 1 u := rfl

theorem hsimple_sound (hM : 1 ≤ M) {c c' : HC} (h : hsimple c = some c') (T : List LS)
    (t : List RI) : simple eagerOps (c.den M T t) = some (c'.den M T t) := by
  obtain ⟨d, l, r⟩ := c
  cases d
  · simp only [hsimple, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hpush_x] at hr'
      simp [HC.den, simple, hpushX_den hM hr' t]
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hpush_D, Option.some.injEq] at hr'
      subst hr'
      simp [HC.den, simple, HL.den]
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hpush_P, Option.some.injEq] at hr'
      subst hr'
      simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hpush_C, Option.some.injEq] at hr'
      subst hr'
      simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · obtain ⟨n', hn', h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h2
      simp [HC.den, simple, HL.den, HN.den_pred hn', hlx_den hM hl' T]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · cases h; simp [HC.den, simple, HL.den]
    · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [hpush_G] at hr'
      simp [HC.den, simple, HL.den, hpushG_den hr' t]
    · cases h
  · simp only [hsimple, ↓reduceIte] at h
    split at h
    · cases h
    · obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [HC.den, simple, hlx_den hM hl' T]
    · cases h; simp [HC.den, simple, HL.den]
    · split at h
      · obtain ⟨n', hn', h2⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h2
        simp [HC.den, simple, HL.den, HN.den_pred hn', hlx_den hM hl' T]
      · cases h; simp [HC.den, simple, HL.den]
      · cases h; simp [HC.den, simple, HL.den]
      · cases h; simp [HC.den, simple, HL.den]
      · cases h
    · split at h
      · cases h
      · obtain ⟨l', hl', h2⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h2
        simp only [hpush_P, Option.some.injEq] at hr'
        subst hr'
        simp [HC.den, simple, hlx_den hM hl' T]
      · split at h
        · obtain ⟨n', hn', h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r4, hr4, h3⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨r5, hr5, rfl⟩ := Option.map_eq_some_iff.mp h3
          simp only [hpush_P, Option.some.injEq] at hr5
          subst hr5
          simp [HC.den, simple, HL.den, HN.den_pred hn', hpushX_den hM hr4 t]
        · obtain ⟨r4, hr4, rfl⟩ := Option.map_eq_some_iff.mp h
          simp [HC.den, simple, HL.den, hunx_den hM hr4 t]
        · obtain ⟨r4, hr4, h3⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r5, hr5, rfl⟩ := Option.map_eq_some_iff.mp h3
          simp only [hpush_P, Option.some.injEq] at hr5
          subst hr5
          simp [HC.den, simple, HL.den, hunx_den hM hr4 t]
        · cases h; simp [HC.den, simple, HL.den]
        · obtain ⟨l', hl', h3⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r4, hr4, h4⟩ := Option.bind_eq_some_iff.mp h3
          obtain ⟨r5, hr5, rfl⟩ := Option.map_eq_some_iff.mp h4
          simp only [hpush_P, hpush_D, Option.some.injEq] at hr4 hr5
          subst hr4 hr5
          simp [HC.den, simple, hlH_den hl' T]
        · cases h
      · obtain ⟨r3, hr3, h3⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r4, hr4, h4⟩ := Option.bind_eq_some_iff.mp h3
        obtain ⟨r5, hr5, h5⟩ := Option.bind_eq_some_iff.mp h4
        obtain ⟨r6, hr6, rfl⟩ := Option.map_eq_some_iff.mp h5
        simp only [hpush_P, hpush_D, Option.some.injEq] at hr4 hr5 hr6
        subst hr4 hr5 hr6
        simp [HC.den, simple, hunx_den hM hr3 t]
      · obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
        have := hlx_den hM hl' T
        simp only [HN.den_pure] at this
        simp [HC.den, simple, this]
      · cases h
    · obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
      simp [HC.den, simple, hlG_den hl' T]

end

/-! ## Batched sweeps split -/

/-- A sweep with multiplier `n₁ + n₂` is a sweep with `n₁` followed by a sweep with `n₂`
(generalized over the accumulated runs). -/
theorem sweep_split (t : List RI) : ∀ (a c n1 n2 : Nat) (u : List RI),
    sweep a (n1 + n2) t = some u →
      ∃ s, sweep a n1 t = some s ∧ sweep c n2 s = some (pushX c u) := by
  induction t with
  | nil => intro a c n1 n2 u h; simp [sweep] at h
  | cons i t ih =>
    intro a c n1 n2 u h
    cases i with
    | x b =>
      simp only [sweep] at h ⊢
      exact ih _ _ _ _ _ h
    | D =>
      rw [sweep_D] at h
      obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨s0, hs0, hs0'⟩ := ih 0 0 n1 n2 u0 hu0
      rw [pushX_zero] at hs0'
      refine ⟨pushX a (.D :: s0), by rw [sweep_D, hs0]; rfl, ?_⟩
      rw [sweep_pushX, sweep_D, hs0', pushX_pushX]
      rfl
    | C =>
      rw [sweep_C] at h
      split_ifs at h with hle
      obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Nat.mul_add] at hu0
      obtain ⟨s0, hs0, hs0'⟩ := ih 0 (2 * n1) (4 * n1) (4 * n2) u0 hu0
      have h1 : n1 ≤ a := by omega
      have h2 : n2 ≤ c + (a - n1) := by omega
      refine ⟨pushX (a - n1) (.C :: pushX (2 * n1) s0), ?_, ?_⟩
      · simp only [sweep_C, h1, ↓reduceIte, hs0, Option.map_some]
      · simp only [sweep_pushX, sweep_C, h2, ↓reduceIte, Nat.zero_add, hs0', Option.map_some,
          pushX_pushX]
        congr 2
        · omega
        · congr 2; omega
    | P =>
      rcases t with _ | ⟨j, t⟩
      · rw [sweep_Pend] at h
        cases h
        refine ⟨pushX a [.P], sweep_Pend _ _, ?_⟩
        rw [sweep_pushX, sweep_Pend, pushX_pushX]
      · rw [sweep_P _ _ _ (List.cons_ne_nil _ _)] at h
        cases h
    | G g =>
      simp only [sweep] at h ⊢
      obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.mp h
      by_cases hg : g = 0
      · subst hg
        obtain ⟨s0, hs0, hs0'⟩ := ih 0 (c + a) n1 n2 u0 hu0
        refine ⟨pushX a (pushG 0 s0), by rw [hs0]; rfl, ?_⟩
        have e0 : ∀ L : List RI, pushG 0 L = L := fun L => by simp [pushG]
        rw [e0, e0, sweep_pushX, hs0', pushX_pushX]
      · obtain ⟨s0, hs0, hs0'⟩ := ih 0 0 n1 n2 u0 hu0
        rw [pushX_zero] at hs0'
        refine ⟨pushX a (pushG g s0), by rw [hs0]; rfl, ?_⟩
        rw [sweep_pushX, sweep_pushG _ _ _ hg, hs0', pushX_pushX]
        rfl

/-! ## Soundness of ticks -/

section
variable {M : Nat}

theorem hsweep_sound (hM : 1 ≤ M) (p : List HRI) : ∀ (a : HN) (n : Nat) (p' : List HRI) (n' : Nat),
    hsweep a n p = some (p', n') → ∀ {t t' : List RI}, sweep 0 n' t = some t' →
      sweep (a.den M) n (p.map (HRI.den M) ++ t) = some (p'.map (HRI.den M) ++ t') := by
  induction p with
  | nil =>
    intro a n p' n' h t t' ht
    simp only [hsweep] at h
    split_ifs at h with hz
    cases h
    simpa [HN.den_zero hz] using ht
  | cons i p ih =>
    intro a n p' n' h t t' ht
    cases i with
    | x b =>
      simp only [hsweep, Option.bind_eq_some_iff] at h
      obtain ⟨a', ha', h1⟩ := h
      simp only [List.map_cons, HRI.den_x, List.cons_append, sweep, ← HN.den_add ha']
      exact ih _ _ _ _ h1 ht
    | D =>
      simp only [hsweep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, p'', hp'', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := ih _ _ _ _ hq ht
      simp only [HN.den_pure] at this
      simp only [List.map_cons, HRI.den_D, List.cons_append, sweep_D, this, Option.map_some]
      rw [← hpushX_den hM hp'' t']
      rfl
    | C =>
      simp only [hsweep] at h
      split_ifs at h with hle
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, t1, ht1, p'', hp'', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := ih _ _ _ _ hq ht
      simp only [HN.den_pure] at this
      have hle' : n ≤ a.den M := by
        obtain ⟨ah, ak⟩ := a
        cases ah <;> simp only [HN.den, Bool.false_eq_true, ↓reduceIte] at * <;> omega
      have e1 := hpushX_den hM ht1 t'
      have e2 := hpushX_den hM hp'' t'
      simp only [HN.den_pure] at e1
      have e3 : HN.den M ⟨a.h, a.k - n⟩ = a.den M - n := by
        obtain ⟨ah, ak⟩ := a
        cases ah <;> simp only [HN.den, Bool.false_eq_true, ↓reduceIte] at *
        omega
      rw [e3] at e2
      simp only [List.map_cons, HRI.den_C, List.cons_append, sweep_C, hle', ↓reduceIte, this,
        Option.map_some, e1]
      rw [← e2]
      rfl
    | G g =>
      simp only [hsweep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, t1, ht1, p'', hp'', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := ih _ _ _ _ hq ht
      simp only [HN.den_pure] at this
      simp only [List.map_cons, HRI.den_G, List.cons_append, sweep, this, Option.map_some,
        hpushG_den ht1 t', hpushX_den hM hp'' t']
    | P => simp [hsweep] at h

theorem hsweep_mono (p : List HRI) : ∀ (a : HN) (n : Nat) (p' : List HRI) (n' : Nat),
    hsweep a n p = some (p', n') → n ≤ n' := by
  induction p with
  | nil =>
    intro a n p' n' h
    simp only [hsweep] at h
    split_ifs at h
    cases h
    exact le_refl _
  | cons i p ih =>
    intro a n p' n' h
    cases i with
    | x b =>
      simp only [hsweep, Option.bind_eq_some_iff] at h
      obtain ⟨a', -, h1⟩ := h
      exact ih _ _ _ _ h1
    | D =>
      simp only [hsweep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, p'', -, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ih _ _ _ _ hq
    | C =>
      simp only [hsweep] at h
      split_ifs at h with hle
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, t1, -, p'', -, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := ih _ _ _ _ hq
      omega
    | G g =>
      simp only [hsweep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨q1, q2⟩, hq, t1, -, p'', -, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ih _ _ _ _ hq
    | P => simp [hsweep] at h

theorem htick_sound (hM : 1 ≤ M) {c c' : HC} {n' : Nat} (h : htick c = some (c', n'))
    (T : List LS) {t t' : List RI} (ht : sweep 0 n' t = some t') :
    tickSt eagerOps (c.den M T t) = some (c'.den M T t') := by
  obtain ⟨d, l, r⟩ := c
  unfold htick at h
  split_ifs at h with hd
  simp only at hd
  subst hd
  obtain ⟨⟨q1, q2⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have := hsweep_sound hM _ _ _ _ _ hq ht
  simp only [HN.den_pure] at this
  show Option.map _ (sweep 0 1 (List.map (HRI.den M) r ++ t)) = _
  rw [this]
  rfl

theorem htick_pos {c c' : HC} {n' : Nat} (h : htick c = some (c', n')) : 1 ≤ n' := by
  unfold htick at h
  split_ifs at h
  obtain ⟨⟨q1, q2⟩, hq, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact hsweep_mono _ _ _ _ _ hq

/-- `d` deferred ticks applied to the abstract right tail (`d = 0`: nothing happens). -/
def sw (d : Nat) (t : List RI) : Option (List RI) := if d = 0 then some t else sweep 0 d t

/-- **Soundness of het runs.**  For every `M ≥ 1`, every left tail `T` and every right
tail `t` that admits the deferred ticks, a het run is a run of simple steps and ticks. -/
theorem hrun_sound (hM : 1 ≤ M) (T : List LS) (k : Nat) : ∀ (c c' : HC) (d : Nat),
    hrun k c = some (c', d) → ∀ {t t' : List RI}, sw d t = some t' →
      Relation.ReflTransGen
        (fun a b : St (List RI) => simple eagerOps a = some b ∨ tickSt eagerOps a = some b)
        (c.den M T t) (c'.den M T t') := by
  induction k with
  | zero =>
    intro c c' d h t t' ht
    simp only [hrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [sw, ↓reduceIte, Option.some.injEq] at ht
    subst ht
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro c c' d h t t' ht
    simp only [hrun, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, d1⟩, h1, ⟨c2, d2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    unfold hstep at h1
    split at h1
    · rename_i p hp
      cases h1
      have hpos := htick_pos hp
      have hne : d1 + d2 ≠ 0 := by omega
      simp only [sw, hne, ↓reduceIte] at ht
      by_cases hd2 : d2 = 0
      · subst hd2
        refine Relation.ReflTransGen.head (Or.inr (htick_sound hM hp T ht)) (ih _ _ _ h2 ?_)
        simp [sw]
      · obtain ⟨s, hs, hs'⟩ := sweep_split t 0 0 d1 d2 t' ht
        rw [pushX_zero] at hs'
        refine Relation.ReflTransGen.head (Or.inr (htick_sound hM hp T hs)) (ih _ _ _ h2 ?_)
        simp [sw, hd2, hs']
    · obtain ⟨c1', hc1, he⟩ := Option.map_eq_some_iff.mp h1
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [Nat.zero_add] at ht
      exact Relation.ReflTransGen.head (Or.inl (hsimple_sound hM hc1 T t)) (ih _ _ _ h2 ht)

/-! ## Concrete left tapes -/

/-- A concrete left symbol as a het symbol (the tail marker never occurs here). -/
def liftLS : LS → HL
  | .x n => .x (.pure n)
  | .D => .D | .P => .P | .C0 => .C0 | .C1 => .C1 | .C2 => .C2 | .C3 => .C3
  | .F0 => .F0 | .F1 => .F1 | .F2 => .F2 | .F3 => .F3
  | .G0 => .G0 | .G1 => .G1 | .G2 => .G2
  | .Fs n => .Fs n | .Gs n => .Gs n | .Hs n => .Hs n
  | .tl => .D

theorem den_liftLS {s : LS} (hs : s ≠ .tl) : (liftLS s).den M = s := by
  cases s <;> simp_all [liftLS, HL.den]

theorem map_den_liftLS {L : List LS} (h : LS.tl ∉ L) : (L.map liftLS).map (HL.den M) = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro s hs
  exact den_liftLS (fun e => h (e ▸ hs))

theorem jc_tl_free : LS.tl ∉ Jc := by decide

end

end Sk1.Het
