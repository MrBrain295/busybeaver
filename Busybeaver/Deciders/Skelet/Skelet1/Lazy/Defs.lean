/-!
# Lazy right tape for the Skelet #1 symbolic simulator

The right tape of the Skelet #1 symbolic simulator is a list of items
`x n | D | C | P | G n` (head-nearest first).  A *tick* (one full sweep of the
head across the right tape and back, the `stride 0 1` of the accelerated
simulator) acts on this tape like a 4-adic multi-level counter:

* the `C` marks split the tape into *levels*; level `j` is ticked with weight
  `4^j`;
* within a level only the last `x`-run before the closing `C` is decremented,
  and only the first `x`-run after it is incremented.

Hence a tick only touches the two runs adjacent to every `C`, linearly in the
number of ticks.  This file introduces a representation of the right tape in
which ticks are *deferred*: every level carries a pending *summary* `(s, r)` of
not-yet-applied ticks, which is pushed one level deeper (scaled by `4`) only
when the head actually needs to look at that level.  A tick is then `O(1)`
instead of `O(length of the right tape)`.
-/

namespace Sk1

/-- Right tape items (head-nearest first). -/
inductive RI
  | x (n : Nat)
  | D
  | C
  | P
  | G (n : Nat)
  deriving DecidableEq, Repr

/-- Separators that may occur inside a level. -/
inductive Sep
  | D
  | G (n : Nat)
  | P
  deriving DecidableEq, Repr

/-- The content of one level: runs followed by separators, and a final run.
`⟨[(a, D), (b, G 3)], t⟩` stands for `x a, D, x b, G 3, x t` (zero runs are absent). -/
structure Seg where
  segs : List (Nat × Sep)
  trail : Nat
  deriving DecidableEq, Repr

/-- A deferred level: its content and the pending tick summary `(s, r)`. -/
structure LBlk where
  body : Seg
  s : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- Lazy right tape: the concrete head level, the deeper (deferred) levels, each
preceded by a `C`, and whether the tape ends with `P`. -/
structure RT where
  top : Seg
  below : List LBlk
  termP : Bool
  deriving DecidableEq, Repr

/-! ## Eager semantics -/

/-- Push `n` copies of `x` on a right tape, merging runs. -/
def pushX (n : Nat) (t : List RI) : List RI :=
  if n = 0 then t else
  match t with
  | .x m :: t => .x (n + m) :: t
  | t => .x n :: t

/-- Push `n` copies of the `G` block on a right tape, merging. -/
def pushG (n : Nat) (t : List RI) : List RI :=
  if n = 0 then t else
  match t with
  | .G m :: t => .G (n + m) :: t
  | t => .G n :: t

/-- The eager sweep: `sweep a n t` processes the right tape `t` with an
accumulated run `a` and multiplier `n` (one tick is `sweep 0 1`). -/
def sweep : Nat → Nat → List RI → Option (List RI)
  | a, _, [.P] => some (pushX a [.P])
  | _, _, .P :: _ => none
  | _, _, [] => none
  | a, n, .x b :: t => sweep (a + b) n t
  | a, n, .D :: t => (sweep 0 n t).map fun t => pushX a (.D :: t)
  | a, n, .C :: t =>
      if n ≤ a then (sweep 0 (4 * n) t).map fun t => pushX (a - n) (.C :: pushX (2 * n) t)
      else none
  | a, n, .G g :: t => (sweep 0 n t).map fun t => pushX a (pushG g t)

/-! ## Flattening -/

def Sep.item : Sep → RI
  | .D => .D
  | .G n => .G n
  | .P => .P

/-- Push a separator on an eager tape (`G` blocks merge, as in the eager sweep). -/
def Sep.push : Sep → List RI → List RI
  | .D, t => .D :: t
  | .G n, t => pushG n t
  | .P, t => .P :: t

/-- Items of a level followed by `t`. -/
def Seg.items (g : Seg) (t : List RI) : List RI :=
  g.segs.foldr (fun p acc => pushX p.1 (p.2.push acc)) (pushX g.trail t)

/-! ## Lazy operations -/

/-- Does a level contain a `P` separator? -/
def Seg.hasP (g : Seg) : Bool := g.segs.any fun p => p.2 == .P

/-- Apply a pending summary `(s, r)` to a level.  `last` tells whether this is
the deepest level (followed by the end of the tape). -/
def Seg.apply (s r : Nat) (last termP : Bool) (g : Seg) : Option Seg :=
  if s = 0 then some g else
  if g.hasP then none else
  if last then
    if termP then
      match g.segs with
      | [] => some ⟨[], g.trail + s⟩
      | (a, sp) :: rest => some ⟨(a + s, sp) :: rest, g.trail⟩
    else none
  else
    match g.segs with
    | [] => if r ≤ g.trail then some ⟨[], g.trail - s⟩ else none
    | (a, sp) :: rest => if 2 * s ≤ g.trail then some ⟨(a + s, sp) :: rest, g.trail - 2 * s⟩ else none

/-- Compose pending summaries: `(s, r)` happened first, then `(s', r')`. -/
def comp (s r s' r' : Nat) : Nat × Nat := (s + s', max r (s + r'))

/-- Add a pending summary `(s, r)` (happening after the existing one) to the
first deferred level. -/
def addPend (s r : Nat) : List LBlk → List LBlk
  | [] => []
  | b :: bs => ⟨b.body, b.s + s, max b.r (b.s + r)⟩ :: bs

/-- One tick of the lazy tape. -/
def RT.tick (t : RT) : Option RT :=
  if t.termP then
    if t.top.hasP then none else
    match t.below with
    | [] => some t
    | b :: bs =>
      if 1 ≤ t.top.trail then
        some ⟨⟨t.top.segs, t.top.trail - 1⟩, ⟨b.body, b.s + 2, max b.r (b.s + 4)⟩ :: bs, true⟩
      else none
  else none

/-- `m` ticks at once (a sweep with multiplier `m`) on the lazy tape. -/
def RT.tickN (m : Nat) (t : RT) : Option RT :=
  if t.termP then
    if t.top.hasP then none else
    match t.below with
    | [] => some t
    | b :: bs =>
      if m ≤ t.top.trail then
        some ⟨⟨t.top.segs, t.top.trail - m⟩, ⟨b.body, b.s + 2 * m, max b.r (b.s + 4 * m)⟩ :: bs, true⟩
      else none
  else none

def Seg.pushX (n : Nat) (g : Seg) : Seg :=
  if n = 0 then g else
  match g.segs with
  | [] => ⟨[], g.trail + n⟩
  | (a, sp) :: rest => ⟨(a + n, sp) :: rest, g.trail⟩

def Seg.pushG (n : Nat) (g : Seg) : Seg :=
  if n = 0 then g else
  match g.segs, g.trail with
  | (0, .G m) :: rest, tr => ⟨(0, .G (n + m)) :: rest, tr⟩
  | segs, tr => ⟨(0, .G n) :: segs, tr⟩

def Seg.isEmpty (g : Seg) : Bool := g.segs.isEmpty && g.trail == 0

/-- Push an item on the lazy tape. -/
def RT.push (t : RT) : RI → RT
  | .x n => ⟨t.top.pushX n, t.below, t.termP⟩
  | .D => ⟨⟨(0, .D) :: t.top.segs, t.top.trail⟩, t.below, t.termP⟩
  | .G n => ⟨t.top.pushG n, t.below, t.termP⟩
  | .P =>
    if t.top.isEmpty && t.below.isEmpty && !t.termP then ⟨t.top, t.below, true⟩
    else ⟨⟨(0, .P) :: t.top.segs, t.top.trail⟩, t.below, t.termP⟩
  | .C => ⟨⟨[], 0⟩, ⟨t.top, 0, 0⟩ :: t.below, t.termP⟩

/-- Pop the head item of the lazy tape, materializing the next level when the
head crosses a `C`. -/
def RT.pop (t : RT) : Option (RI × RT) :=
  match t.top.segs with
  | (a, sp) :: rest =>
    if a = 0 then some (sp.item, ⟨⟨rest, t.top.trail⟩, t.below, t.termP⟩)
    else some (.x a, ⟨⟨(0, sp) :: rest, t.top.trail⟩, t.below, t.termP⟩)
  | [] =>
    if t.top.trail = 0 then
      match t.below with
      | b :: bs =>
        match b.body.apply b.s b.r bs.isEmpty t.termP with
        | some g => some (.C, ⟨g, addPend (4 * b.s) (4 * b.r) bs, t.termP⟩)
        | none => none
      | [] => if t.termP then some (.P, ⟨t.top, [], false⟩) else none
    else some (.x t.top.trail, ⟨⟨[], 0⟩, t.below, t.termP⟩)

/-- Materialize every level: the list of concrete levels. -/
def matBelow (termP : Bool) : Nat → Nat → List LBlk → Option (List Seg)
  | _, _, [] => some []
  | s, r, b :: bs =>
    let (s', r') := comp b.s b.r s r
    match b.body.apply s' r' bs.isEmpty termP with
    | some g => (matBelow termP (4 * s') (4 * r') bs).map (g :: ·)
    | none => none

/-- Flatten concrete levels (each preceded by `C`). -/
def flatBelow (termP : Bool) : List Seg → List RI
  | [] => if termP then [.P] else []
  | g :: gs => .C :: g.items (flatBelow termP gs)

/-- Denotation of a lazy tape: the eager right tape it stands for. -/
def RT.den (t : RT) : Option (List RI) :=
  (matBelow t.termP 0 0 t.below).map fun gs => t.top.items (flatBelow t.termP gs)

end Sk1
