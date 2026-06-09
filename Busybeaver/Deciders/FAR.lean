import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Std.Data.HashSet

open TM.Table

namespace Deciders.FAR

abbrev U := Nat
abbrev OStU := Option (Label 4 × U)
abbrev NFAEntry := OStU × Symbol 1 × OStU
abbrev NFASet := Std.HashSet Nat
abbrev AccSet := Std.HashSet Nat

structure Config where
  states : Nat
  dfa : Array (Nat × Nat)

def Config.uList (cfg : Config) : List U :=
  List.range (cfg.states + 1)

def labels : List (Label 4) :=
  List.finRange 5

def symbols : List (Symbol 1) :=
  List.finRange 2

def optionStates (cfg : Config) : List OStU :=
  none :: (labels.flatMap fun st => cfg.uList.map fun u => some (st, u))

def Config.step (cfg : Config) (u : U) (sym : Symbol 1) : U :=
  let pair := cfg.dfa.getD u (0, 0)
  if sym.val = 0 then pair.1 else pair.2

def optionCount (cfg : Config) : Nat :=
  1 + 5 * (cfg.states + 1)

def encodeOStU (cfg : Config) : OStU → Nat
  | none => 0
  | some (st, u) => 1 + st.val * (cfg.states + 1) + u

def encodeEntry (cfg : Config) (entry : NFAEntry) : Nat :=
  let src := encodeOStU cfg entry.1
  let sym := entry.2.1.val
  let dst := encodeOStU cfg entry.2.2
  (src * 2 + sym) * optionCount cfg + dst

def nfaContains (cfg : Config) (nfa : NFASet) (entry : NFAEntry) : Bool :=
  nfa.contains (encodeEntry cfg entry)

def accContains (cfg : Config) (acc : AccSet) (state : OStU) : Bool :=
  acc.contains (encodeOStU cfg state)

def insertEntry (cfg : Config) (entry : NFAEntry) (nfa : NFASet) : NFASet × Bool :=
  let key := encodeEntry cfg entry
  if nfa.contains key then
    (nfa, false)
  else
    (nfa.insert key, true)

def insertAcc (cfg : Config) (state : OStU) (acc : AccSet) : AccSet × Bool :=
  let key := encodeOStU cfg state
  if acc.contains key then
    (acc, false)
  else
    (acc.insert key, true)

def initialNFA (cfg : Config) (M : Machine 4 1) : NFASet :=
  Id.run do
    let mut nfa : NFASet := Std.HashSet.emptyWithCapacity 4096
    for i0 in symbols do
      nfa := (insertEntry cfg (none, i0, none) nfa).1
    for s0 in labels do
      for u0 in cfg.uList do
        for i0 in symbols do
          match M.get s0 i0 with
          | .halt =>
              nfa := (insertEntry cfg (some (s0, u0), i0, none) nfa).1
          | _ => nfa := nfa
    for s0 in labels do
      for i0 in symbols do
        match M.get s0 i0 with
        | .next i1 .right s1 =>
            for u0 in cfg.uList do
              nfa := (insertEntry cfg (some (s0, u0), i0, some (s1, cfg.step u0 i1)) nfa).1
        | _ => nfa := nfa
    nfa

def closeLeftStep (cfg : Config) (M : Machine 4 1) (nfa : NFASet) : NFASet × Bool :=
  Id.run do
    let mut cur := nfa
    let mut changed := false
    for s0 in labels do
      for i0 in symbols do
        match M.get s0 i0 with
        | .next i1 .left s1 =>
            for u1 in cfg.uList do
              for i2 in symbols do
                for su2 in optionStates cfg do
                  if nfaContains cfg cur (some (s1, u1), i2, su2) then
                    for su3 in optionStates cfg do
                      if nfaContains cfg cur (su2, i1, su3) then
                        let entry := (some (s0, cfg.step u1 i2), i0, su3)
                        let (next, inserted) := insertEntry cfg entry cur
                        cur := next
                        changed := changed || inserted
        | _ => cur := cur
    (cur, changed)

def closeLeft : Nat → Config → Machine 4 1 → NFASet → NFASet
  | 0, _, _, nfa => nfa
  | fuel + 1, cfg, M, nfa =>
      let (next, changed) := closeLeftStep cfg M nfa
      if changed then
        closeLeft fuel cfg M next
      else
        next

def buildNFA (maxT : Nat) (cfg : Config) (M : Machine 4 1) : NFASet :=
  closeLeft maxT cfg M (initialNFA cfg M)

def closeAccStep (cfg : Config) (nfa : NFASet) (acc : AccSet) : AccSet × Bool :=
  Id.run do
    let mut cur := acc
    let mut changed := false
    for su0 in optionStates cfg do
      for su1 in optionStates cfg do
        if nfaContains cfg nfa (su0, (0 : Symbol 1), su1) && accContains cfg cur su0 then
          let (next, inserted) := insertAcc cfg su1 cur
          cur := next
          changed := changed || inserted
    (cur, changed)

def closeAcc : Nat → Config → NFASet → AccSet → AccSet
  | 0, _, _, acc => acc
  | fuel + 1, cfg, nfa, acc =>
      let (next, changed) := closeAccStep cfg nfa acc
      if changed then
        closeAcc fuel cfg nfa next
      else
        next

def buildAcc (maxT : Nat) (cfg : Config) (nfa : NFASet) : AccSet :=
  let initial : AccSet := Std.HashSet.emptyWithCapacity 128
  closeAcc maxT cfg nfa ((insertAcc cfg (some (default, 0)) initial).1)

def checkConditions (cfg : Config) (M : Machine 4 1) (nfa : NFASet) (acc : AccSet) : Bool :=
  let h0 :=
    symbols.all fun i0 => nfaContains cfg nfa (none, i0, none)
  let h :=
    labels.all fun s0 =>
      cfg.uList.all fun u0 =>
        symbols.all fun i0 =>
          match M.get s0 i0 with
          | .halt => nfaContains cfg nfa (some (s0, u0), i0, none)
          | _ => true
  let r :=
    labels.all fun s0 =>
      cfg.uList.all fun u0 =>
        symbols.all fun i0 =>
          match M.get s0 i0 with
          | .next i1 .right s1 => nfaContains cfg nfa (some (s0, u0), i0, some (s1, cfg.step u0 i1))
          | _ => true
  let l :=
    labels.all fun s0 =>
      symbols.all fun i0 =>
        match M.get s0 i0 with
        | .next i1 .left s1 =>
            cfg.uList.all fun u1 =>
              symbols.all fun i2 =>
                (optionStates cfg).all fun su2 =>
                  (optionStates cfg).all fun su3 =>
                    if nfaContains cfg nfa (some (s1, u1), i2, su2) then
                      if nfaContains cfg nfa (su2, i1, su3) then
                        nfaContains cfg nfa (some (s0, cfg.step u1 i2), i0, su3)
                      else
                        true
                    else
                      true
        | _ => true
  let dfa0 := cfg.step 0 (0 : Symbol 1) == 0
  let acc0 := accContains cfg acc (some (default, 0))
  let accH := !(accContains cfg acc none)
  let accClosed :=
    (optionStates cfg).all fun su0 =>
      (optionStates cfg).all fun su1 =>
        if nfaContains cfg nfa (su0, (0 : Symbol 1), su1) then
          if accContains cfg acc su0 then accContains cfg acc su1 else true
        else
          true
  h0 && h && r && l && dfa0 && acc0 && accH && accClosed

def run (maxT : Nat) (cfg : Config) (M : Machine 4 1) : Bool :=
  let nfa := buildNFA maxT cfg M
  let acc := buildAcc maxT cfg nfa
  checkConditions cfg M nfa acc

private theorem run_eq_true_nonHalting
    (maxT : Nat) (cfg : Config) (M : Machine 4 1)
    (h : run maxT cfg M = true) :
    ¬M.halts TM.Table.init := by
  sorry

def decider (maxT : Nat) (cfg : Config) (M : Machine 4 1) : HaltM M Unit :=
  if h : run maxT cfg M = true then
    .loops_prf (run_eq_true_nonHalting maxT cfg M h)
  else
    .unknown ()

end Deciders.FAR
