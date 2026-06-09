import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability

open TM.Table

namespace Deciders.Loop1

structure HistoryEntry (l s : ℕ) where
  cfg : Config l s
  pos : Int
deriving DecidableEq

def dirDelta : Turing.Dir → Int
  | .left => -1
  | .right => 1

def sameStateHead (a b : HistoryEntry l s) : Bool :=
  decide (a.cfg.state = b.cfg.state) && decide (a.cfg.tape.head = b.cfg.tape.head)

def noVisitedRight (h : HistoryEntry l s) : Bool :=
  decide (h.cfg.tape.right = (default : Turing.ListBlank (Symbol s)))

def noVisitedLeft (h : HistoryEntry l s) : Bool :=
  decide (h.cfg.tape.left = (default : Turing.ListBlank (Symbol s)))

def baseLoopCheck (h0 h1 : HistoryEntry l s) (n : ℕ) (dpos : Int) : Bool :=
  n == 0 && (
    if dpos = 0 then
      decide (h1.pos = h0.pos)
    else if dpos > 0 then
      noVisitedRight h1 && decide (h1.pos < h0.pos)
    else
      noVisitedLeft h1 && decide (h0.pos < h1.pos)
  )

def verifyLoop1 (h0 h1 : HistoryEntry l s) :
    List (HistoryEntry l s) → List (HistoryEntry l s) → ℕ → Int → Bool
  | h0' :: ls0', h1' :: ls1', n, dpos =>
      sameStateHead h0 h1 && (
        baseLoopCheck h0 h1 n dpos ||
        verifyLoop1 h0' h1' ls0' ls1' n.pred dpos
      )
  | _, _, n, dpos =>
      sameStateHead h0 h1 && baseLoopCheck h0 h1 n dpos

def findLoop1 (h0 h1 h2 : HistoryEntry l s) (ls0 : List (HistoryEntry l s)) :
    List (HistoryEntry l s) → List (HistoryEntry l s) → ℕ → Bool
  | h1' :: ls1', _ :: h2' :: ls2', n =>
      (
        sameStateHead h0 h1 &&
        sameStateHead h0 h2 &&
        verifyLoop1 h0 h1 ls0 (h1' :: ls1') (n + 1) (h0.pos - h1.pos)
      ) ||
      findLoop1 h0 h1' h2' ls0 ls1' ls2' (n + 1)
  | _, _, n =>
      sameStateHead h0 h1 &&
      sameStateHead h0 h2 &&
      verifyLoop1 h0 h1 ls0 [] (n + 1) (h0.pos - h1.pos)
termination_by ls1 _ _ => ls1.length

def findLoop10 (h0 h1 : HistoryEntry l s) : List (HistoryEntry l s) → Bool
  | h2 :: ls' => findLoop1 h0 h1 h2 (h1 :: h2 :: ls') (h2 :: ls') ls' 0
  | [] => false

def step? (M : Machine l s) (h : HistoryEntry l s) : Option (HistoryEntry l s) :=
  match M.get h.cfg.state h.cfg.tape.head with
  | .halt => none
  | .next sym dir state =>
      some {
        cfg := { state, tape := h.cfg.tape.write sym |>.move dir }
        pos := h.pos + dirDelta dir
      }

def runFrom (M : Machine l s) : ℕ → HistoryEntry l s → List (HistoryEntry l s) → Bool
  | 0, _, _ => false
  | fuel + 1, cur, history =>
      match step? M cur with
      | none => false
      | some next =>
          match fuel with
          | 0 => findLoop10 next cur history
          | _ + 1 => runFrom M fuel next (cur :: history)

def run (bound : ℕ) (M : Machine l s) : Bool :=
  runFrom M bound { cfg := init, pos := 0 } []

private theorem run_eq_true_nonHalting
    (bound : ℕ) (M : Machine l s)
    (h : run bound M = true) :
    ¬M.halts TM.Table.init := by
  sorry

def decider (bound : ℕ) (M : Machine l s) : HaltM M Unit :=
  if h : run bound M = true then
    .loops_prf (run_eq_true_nonHalting bound M h)
  else
    .unknown ()

end Deciders.Loop1
