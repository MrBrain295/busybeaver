import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Sim

/-!
# Lazy right tape, version 2 (kernel-oriented)

* The head level is a plain list of items (`top`), so pushes and pops at the
  head are list operations.
* Ticks at level 0 are deferred too: `k` counts ticks not yet applied to the
  last run of `top`.  A tick is therefore `k + 1` plus two `O(1)` checks
  (`pc = 0`: no `P` in the head level; `termP`: the tape ends with `P`).
* Deeper levels are plain lists of items with a pending summary `(s, r)`.
-/

namespace Sk1

structure LB where
  items : List RI
  s : Nat
  r : Nat
  deriving DecidableEq, Repr

structure RT2 where
  top : List RI
  k : Nat
  pc : Nat
  below : List LB
  termP : Bool
  deriving DecidableEq, Repr

/-- Apply `k` deferred level-0 ticks to the last run of a level. -/
def lastSub (k : Nat) : List RI → Option (List RI)
  | [] => none
  | [.x t] => if k ≤ t then some (if t = k then [] else [.x (t - k)]) else none
  | [_] => none
  | i :: t => (lastSub k t).map (i :: ·)

/-- Apply a pending summary to a non-final level given as a list of items. -/
def applyMid (s r : Nat) : List RI → Option (List RI)
  | [] => if r = 0 then some [] else none
  | [.x v] => if r ≤ v then some (if v = s then [] else [.x (v - s)]) else none
  | .x a :: t => (lastSub (2 * s) t).map (.x (a + s) :: ·)
  | i :: t => (lastSub (2 * s) (i :: t)).map (.x s :: ·)

def noP : List RI → Bool
  | [] => true
  | .P :: _ => false
  | _ :: t => noP t

/-- Apply a pending summary `(s, r)` to a level. -/
def applyLB (s r : Nat) (last termP : Bool) (items : List RI) : Option (List RI) :=
  if s = 0 then some items else
  if noP items then
    if last then (if termP then some (pushX s items) else none)
    else applyMid s r items
  else none

def addPend2 (s r : Nat) : List LB → List LB
  | [] => []
  | b :: bs => ⟨b.items, b.s + s, max b.r (b.s + r)⟩ :: bs

/-- Force the deferred level-0 ticks. -/
def RT2.force (t : RT2) : Option RT2 :=
  if t.k = 0 then some t else
  (lastSub t.k t.top).map fun top =>
    ⟨top, 0, t.pc, addPend2 (2 * t.k) (2 * t.k + 2) t.below, t.termP⟩

def countP : List RI → Nat
  | [] => 0
  | .P :: t => countP t + 1
  | _ :: t => countP t

def RT2.tick (t : RT2) : Option RT2 :=
  if t.termP then
    if t.pc = 0 then
      match t.below with
      | [] => some t
      | _ :: _ => some ⟨t.top, t.k + 1, t.pc, t.below, t.termP⟩
    else none
  else none

/-- Push an item. -/
def RT2.push (t : RT2) (i : RI) : RT2 :=
  match i with
  | .x n =>
    if n = 0 then t else
    match t.top with
    | [] | [.x _] =>
      match t.force with
      | some u => ⟨pushX n u.top, 0, u.pc, u.below, u.termP⟩
      | none => ⟨[.x 0], 0, 0, [], false⟩  -- unreachable on valid traces; makes `den` fail
    | .x m :: rest => ⟨.x (n + m) :: rest, t.k, t.pc, t.below, t.termP⟩
    | top => ⟨.x n :: top, t.k, t.pc, t.below, t.termP⟩
  | .G n => ⟨pushG n t.top, t.k, t.pc, t.below, t.termP⟩
  | .D => ⟨.D :: t.top, t.k, t.pc, t.below, t.termP⟩
  | .P =>
    match t.top, t.below, t.termP with
    | [], [], false => ⟨[], t.k, t.pc, [], true⟩
    | _, _, _ => ⟨.P :: t.top, t.k, t.pc + 1, t.below, t.termP⟩
  | .C =>
    match t.force with
    | some u => ⟨[], 0, 0, ⟨u.top, 0, 0⟩ :: u.below, u.termP⟩
    | none => ⟨[.x 0], 0, 0, [], false⟩

/-- Pop the head item. -/
def RT2.pop (t : RT2) : Option (RI × RT2) :=
  match t.top with
  | i :: (j :: rest) =>
    some (i, ⟨j :: rest, t.k, (match i with | .P => t.pc - 1 | _ => t.pc), t.below, t.termP⟩)
  | _ =>
    match t.force with
    | none => none
    | some u =>
      match u.top with
      | [i] => some (i, ⟨[], 0, (match i with | .P => u.pc - 1 | _ => u.pc), u.below, u.termP⟩)
      | _ =>
        match u.below with
        | b :: bs =>
          match applyLB b.s b.r bs.isEmpty u.termP b.items with
          | some its => some (.C, ⟨its, 0, countP its, addPend2 (4 * b.s) (4 * b.r) bs, u.termP⟩)
          | none => none
        | [] => if u.termP then some (.P, ⟨[], 0, 0, [], false⟩) else none

def RT2.ofList (t : List RI) : RT2 := t.foldr (fun i acc => acc.push i) ⟨[], 0, 0, [], false⟩

/-- Materialize all deferred levels. -/
def matB2 (termP : Bool) : Nat → Nat → List LB → Option (List (List RI))
  | _, _, [] => some []
  | s, r, b :: bs =>
    let p := comp b.s b.r s r
    match applyLB p.1 p.2 bs.isEmpty termP b.items with
    | some its => (matB2 termP (4 * p.1) (4 * p.2) bs).map (its :: ·)
    | none => none

def flatB2 (termP : Bool) : List (List RI) → List RI
  | [] => if termP then [.P] else []
  | g :: gs => .C :: (g ++ flatB2 termP gs)

def RT2.den (t : RT2) : Option (List RI) :=
  match t.force with
  | none => none
  | some u => (matB2 u.termP 0 0 u.below).map fun gs => u.top ++ flatB2 u.termP gs

def lazy2 : ROps RT2 where
  pop := RT2.pop
  push := RT2.push
  tick := RT2.tick
  toList := RT2.den
  ofList := RT2.ofList

end Sk1
