import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Std.Data.HashSet

open TM.Table

namespace Deciders.WFAR

inductive GapDir where
  | none
  | left
  | right
deriving DecidableEq, BEq, Hashable

def GapDir.delta : GapDir → Int
  | .none => 0
  | .left => -1
  | .right => 1

def dirDelta : Turing.Dir → Int
  | .left => -1
  | .right => 1

abbrev WTrans := (Nat × Int) × (Nat × Int)

structure WDFA where
  states : Nat
  trans : Array WTrans

structure Config where
  maxD : Nat
  left : WDFA
  right : WDFA
  bound : Nat

structure ES where
  leftState : Nat
  rightState : Nat
  head : Symbol 1
  state : Label 4
  diff : Int
  gap : GapDir
deriving DecidableEq, BEq, Hashable

abbrev ESSet := Std.HashSet ES
abbrev NatSet := Std.HashSet Nat

def WDFA.uList (w : WDFA) : List Nat :=
  List.range (w.states + 1)

def symbols : List (Symbol 1) :=
  List.finRange 2

def WDFA.step (w : WDFA) (u : Nat) (sym : Symbol 1) : Nat × Int :=
  let pair := w.trans.getD u ((0, 0), (0, 0))
  if sym.val = 0 then pair.1 else pair.2

def WDFA.pop (w : WDFA) (target : Nat) : List (Nat × Symbol 1 × Int) :=
  symbols.flatMap fun sym =>
    w.uList.filterMap fun u =>
      let step := w.step u sym
      if step.1 = target then
        some (u, sym, step.2)
      else
        none

def insertNat (x : Nat) (set : NatSet) : NatSet × Bool :=
  if set.contains x then
    (set, false)
  else
    (set.insert x, true)

def insertES (x : ES) (set : ESSet) (queue : List ES) : ESSet × List ES :=
  if set.contains x then
    (set, queue)
  else
    (set.insert x, x :: queue)

def wdfaSgnStep (w : WDFA) (dir : Turing.Dir) (set : NatSet) : NatSet × Bool :=
  Id.run do
    let mut cur := set
    let mut changed := false
    for u0 in w.uList do
      for sym in symbols do
        let step := w.step u0 sym
        if step.2 * dirDelta dir >= 0 && !(cur.contains u0) then
          cur := cur
        else
          let (next, inserted) := insertNat step.1 cur
          cur := next
          changed := changed || inserted
    (cur, changed)

def wdfaSgnSet : Nat → WDFA → Turing.Dir → NatSet → NatSet
  | 0, _, _, set => set
  | fuel + 1, w, dir, set =>
      let (next, changed) := wdfaSgnStep w dir set
      if changed then
        wdfaSgnSet fuel w dir next
      else
        next

def wdfaSgn (fuel : Nat) (w : WDFA) (dir : Turing.Dir) (u : Nat) : Bool :=
  !(wdfaSgnSet fuel w dir (Std.HashSet.emptyWithCapacity 128)).contains u

def wdfa0 (w : WDFA) : Bool :=
  w.step 0 (0 : Symbol 1) == (0, 0)

def wdfaSgnClosed (fuel : Nat) (w : WDFA) (dir : Turing.Dir) : Bool :=
  w.uList.all fun u0 =>
    if wdfaSgn fuel w dir u0 then
      w.uList.all fun u1 =>
        symbols.all fun sym =>
          let step := w.step u1 sym
          if step.1 = u0 then
            step.2 * dirDelta dir >= 0 && wdfaSgn fuel w dir u1
          else
            true
    else
      true

def good (sgnL sgnR : Turing.Dir → Nat → Bool) (es : ES) : Bool :=
  !(
    (es.diff > 0 && es.gap.delta >= 0 && sgnL .left es.leftState && sgnR .left es.rightState) ||
    (es.diff < 0 && es.gap.delta <= 0 && sgnL .right es.leftState && sgnR .right es.rightState)
  )

def simplify (cfg : Config) (es : ES) : List ES :=
  match es.gap with
  | .none =>
      if es.diff.natAbs >= cfg.maxD then
        if es.diff > 0 then
          [{ es with gap := .right }]
        else if es.diff < 0 then
          [{ es with gap := .left }]
        else
          [es]
      else
        [es]
  | gap =>
      let absd := es.diff.natAbs
      if absd > cfg.maxD then
        [{ es with diff := es.diff - gap.delta }]
      else if absd < cfg.maxD then
        [{ es with gap := .none }, { es with diff := es.diff + gap.delta }]
      else
        [es]

def filterSimplify (cfg : Config)
    (sgnL sgnR : Turing.Dir → Nat → Bool) (states : List ES) : List ES :=
  states.filter (good sgnL sgnR) |>.flatMap (simplify cfg)

def successors (cfg : Config) (M : Machine 4 1)
    (sgnL sgnR : Turing.Dir → Nat → Bool) (es : ES) : Option (List ES) :=
  match M.get es.state es.head with
  | .halt => none
  | .next out .right state' =>
      let leftStep := cfg.left.step es.leftState out
      let candidates :=
        (cfg.right.pop es.rightState).map fun (rightState', head', dr) =>
          {
            leftState := leftStep.1
            rightState := rightState'
            head := head'
            state := state'
            diff := es.diff + leftStep.2 - dr
            gap := es.gap
          }
      some (filterSimplify cfg sgnL sgnR candidates)
  | .next out .left state' =>
      let rightStep := cfg.right.step es.rightState out
      let candidates :=
        (cfg.left.pop es.leftState).map fun (leftState', head', dl) =>
          {
            leftState := leftState'
            rightState := rightStep.1
            head := head'
            state := state'
            diff := es.diff + rightStep.2 - dl
            gap := es.gap
          }
      some (filterSimplify cfg sgnL sgnR candidates)

def insertAll (items : List ES) (seen : ESSet) (queue : List ES) : ESSet × List ES :=
  items.foldl (fun (acc : ESSet × List ES) item => insertES item acc.1 acc.2) (seen, queue)

def search (cfg : Config) (M : Machine 4 1)
    (sgnL sgnR : Turing.Dir → Nat → Bool) : Nat → List ES → ESSet → Bool
  | 0, queue, _ => queue.isEmpty
  | _ + 1, [], _ => true
  | fuel + 1, es :: queue, seen =>
      match successors cfg M sgnL sgnR es with
      | none => false
      | some next =>
          let (seen', queue') := insertAll next seen queue
          search cfg M sgnL sgnR fuel queue' seen'

def run (cfg : Config) (M : Machine 4 1) : Bool :=
  let sgnL := wdfaSgn cfg.bound cfg.left
  let sgnR := wdfaSgn cfg.bound cfg.right
  if !(wdfa0 cfg.left) || !(wdfa0 cfg.right) ||
      !(wdfaSgnClosed cfg.bound cfg.left .left) ||
      !(wdfaSgnClosed cfg.bound cfg.left .right) ||
      !(wdfaSgnClosed cfg.bound cfg.right .left) ||
      !(wdfaSgnClosed cfg.bound cfg.right .right) then
    false
  else
    let init : ES := {
      leftState := 0
      rightState := 0
      head := 0
      state := default
      diff := 0
      gap := .none
    }
    let seen : ESSet := (Std.HashSet.emptyWithCapacity 4096).insert init
    search cfg M sgnL sgnR cfg.bound [init] seen

private theorem run_eq_true_nonHalting
    (cfg : Config) (M : Machine 4 1)
    (h : run cfg M = true) :
    ¬M.halts TM.Table.init := by
  sorry

def decider (cfg : Config) (M : Machine 4 1) : HaltM M Unit :=
  if h : run cfg M = true then
    .loops_prf (run_eq_true_nonHalting cfg M h)
  else
    .unknown ()

end Deciders.WFAR
