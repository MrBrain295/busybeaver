import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability

open TM.Table

structure RepWLConfig where
  len : ℕ
  threshold : ℕ
  maxT : ℕ
  bound : ℕ
deriving DecidableEq, Repr

namespace Deciders.RepWL

abbrev Word (s : ℕ) := List (Symbol s)

structure RepeatWord (s : ℕ) where
  w : Word s
  minCnt : ℕ
  isConst : Bool
deriving DecidableEq, Repr

structure ListES (l s : ℕ) where
  left : List (Symbol s)
  right : List (Symbol s)
  head : Symbol s
  state : Label l
deriving DecidableEq, Repr

structure RepWLES (l s : ℕ) where
  left : List (RepeatWord s)
  right : List (RepeatWord s)
  state : Label l
  sgn : Turing.Dir
deriving DecidableEq, Repr

def initial : RepWLES l s := {
  left := []
  right := []
  state := default
  sgn := .right
}

def allBlank (w : Word s) : Bool :=
  w.all (· == default)

def push (cfg : RepWLConfig) (wl : List (RepeatWord s)) (w0 : Word s) :
    List (RepeatWord s) :=
  match wl with
  | v :: wl0 =>
      if v.w = w0 then
        let cnt := v.minCnt + 1
        if cnt < cfg.threshold then
          { w := w0, minCnt := cnt, isConst := v.isConst } :: wl0
        else
          { w := w0, minCnt := cfg.threshold, isConst := false } :: wl0
      else
        { w := w0, minCnt := 1, isConst := true } :: wl
  | [] =>
      if allBlank w0 then
        []
      else
        [{ w := w0, minCnt := 1, isConst := true }]

def pop (cfg : RepWLConfig) (wl : List (RepeatWord s)) :
    Option (Word s × List (List (RepeatWord s))) :=
  match wl with
  | [] => some (List.replicate cfg.len default, [[]])
  | v :: wl0 =>
      match v.minCnt with
      | 0 => none
      | n + 1 =>
          let rest :=
            match n with
            | 0 => wl0
            | _ + 1 => { w := v.w, minCnt := n, isConst := true } :: wl0
          some (v.w, rest :: if v.isConst then [] else [wl])

def wordUpdateStep (M : Machine l s) (x : ListES l s) :
    Option (ListES l s × Option Turing.Dir) :=
  match M.get x.state x.head with
  | .halt => none
  | .next out .right nextState =>
      match x.right with
      | m1 :: r1 =>
          some ({ left := out :: x.left, right := r1, head := m1, state := nextState }, none)
      | [] =>
          some ({ left := x.left, right := [], head := out, state := nextState }, some .right)
  | .next out .left nextState =>
      match x.left with
      | m1 :: l1 =>
          some ({ left := l1, right := out :: x.right, head := m1, state := nextState }, none)
      | [] =>
          some ({ left := [], right := x.right, head := out, state := nextState }, some .left)

def wordUpdateSteps (M : Machine l s) : ListES l s → ℕ → Option (ListES l s × Turing.Dir)
  | _, 0 => none
  | x, n + 1 =>
      match wordUpdateStep M x with
      | some (x0, none) => wordUpdateSteps M x0 n
      | some (x0, some d) => some (x0, d)
      | none => none

def wordUpdate (cfg : RepWLConfig) (M : Machine l s)
    (state : Label l) (w0 : Word s) (sgn : Turing.Dir) :
    Option (Label l × Word s × Bool) :=
  match w0 with
  | [] => none
  | m0 :: w1 =>
      let start : ListES l s :=
        match sgn with
        | .right => { left := [], right := w1, head := m0, state }
        | .left => { left := w1, right := [], head := m0, state }
      match wordUpdateSteps M start cfg.maxT with
      | none => none
      | some (x1, d) =>
          match d with
          | .right => some (x1.state, x1.head :: x1.left, decide (sgn ≠ d))
          | .left => some (x1.state, x1.head :: x1.right, decide (sgn ≠ d))

def stepOne (cfg : RepWLConfig) (M : Machine l s)
    (x : RepWLES l s) (w0 : Word s) (r1 : List (RepeatWord s)) :
    Option (RepWLES l s) :=
  match wordUpdate cfg M x.state w0 x.sgn with
  | none => none
  | some (state1, w1, isBack) =>
      if isBack then
        some {
          left := push cfg r1 w1
          right := x.left
          state := state1
          sgn := x.sgn.other
        }
      else
        some {
          left := push cfg x.left w1
          right := r1
          state := state1
          sgn := x.sgn
        }

def stepAll (cfg : RepWLConfig) (M : Machine l s)
    (x : RepWLES l s) (w0 : Word s) :
    List (List (RepeatWord s)) → Option (List (RepWLES l s))
  | [] => some []
  | r1 :: rest =>
      match stepOne cfg M x w0 r1, stepAll cfg M x w0 rest with
      | some x1, some xs => some (x1 :: xs)
      | _, _ => none

def step (cfg : RepWLConfig) (M : Machine l s) (x : RepWLES l s) :
    Option (List (RepWLES l s)) :=
  match pop cfg x.right with
  | none => none
  | some (w0, branches) => stepAll cfg M x w0 branches

def insertNew [DecidableEq α] (queue : List α) (seen : Array α) (x : α) :
    List α × Array α :=
  if x ∈ seen then
    (queue, seen)
  else
    (x :: queue, seen.push x)

def insertAllNew [DecidableEq α] (queue : List α) (seen : Array α) :
    List α → List α × Array α
  | [] => (queue, seen)
  | x :: xs =>
      let (queue', seen') := insertNew queue seen x
      insertAllNew queue' seen' xs

def search (cfg : RepWLConfig) (M : Machine l s) : ℕ → List (RepWLES l s) →
    Array (RepWLES l s) → Bool
  | 0, queue, _ => queue.isEmpty
  | _ + 1, [], _ => true
  | n + 1, x :: queue, seen =>
      match step cfg M x with
      | none => false
      | some xs =>
          let (queue', seen') := insertAllNew queue seen xs
          search cfg M n queue' seen'

def run (cfg : RepWLConfig) (M : Machine l s) : Bool :=
  search cfg M cfg.bound [initial] #[initial]

private theorem run_eq_true_nonHalting
    (cfg : RepWLConfig) (M : Machine l s)
    (h : run cfg M = true) :
    ¬M.halts TM.Table.init := by
  sorry

def decider (cfg : RepWLConfig) (M : Machine l s) : HaltM M Unit :=
  if h : run cfg M = true then
    .loops_prf (run_eq_true_nonHalting cfg M h)
  else
    .unknown ()

end Deciders.RepWL
