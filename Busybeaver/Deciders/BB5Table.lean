import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.FAR
import Busybeaver.Deciders.Loop1
import Busybeaver.Deciders.NGramCPS
import Busybeaver.Deciders.RepWL
import Busybeaver.Deciders.WFAR
import Std.Data.HashMap

/-!
Executable support for the BB(5) table-based layer.

The Coq BB5 proof uses a small generic pipeline followed by a lookup table for
machines requiring custom parameters, verifiers, or individual nonhalting
arguments.  This file defines the Lean-side shape of that table and the
algorithmic evaluator for the entries we already have executable support for.

The large Coq parameter lists are intentionally not copied here by hand.  They
are generated into `Entry` values by `scripts/generate_bb5_table.py`.
-/

open TM.Table

namespace Deciders.BB5Table

inductive EntryDecider where
  | nGram : (history : ℕ) → (len : ℕ) → (bound : ℕ) → EntryDecider
  | nGramLRU : (len : ℕ) → (bound : ℕ) → EntryDecider
  | repWL : (len : ℕ) → (threshold : ℕ) → (maxT : ℕ) → (bound : ℕ) → EntryDecider
  | halt : (bound : ℕ) → EntryDecider
  | loop1 : (bound : ℕ) → EntryDecider
  | far : (states : ℕ) → (dfa : List (ℕ × ℕ)) → EntryDecider
  | wfar :
      (maxD : ℕ) →
      (leftStates : ℕ) → (left : List ((ℕ × Int) × (ℕ × Int))) →
      (rightStates : ℕ) → (right : List ((ℕ × Int) × (ℕ × Int))) →
      (bound : ℕ) → EntryDecider
  | sporadic : EntryDecider
  | unsupported : String → EntryDecider
deriving DecidableEq, Repr

abbrev Entry := String × EntryDecider
abbrev Table := Std.HashMap String EntryDecider

private theorem sporadic_nonHalting (M : Machine 4 1) :
    ¬M.halts TM.Table.init := by
  sorry

def haltDecider (bound : ℕ) (M : Machine l s) : HaltM M Unit := do
  let _ ← TM.Table.boundedExplore bound M
  .unknown ()

def EntryDecider.run (d : EntryDecider) (M : Machine 4 1) : HaltM M Unit :=
  match d with
  | .nGram 0 len bound =>
      nGramCPSDecider { n := len, bound } M
  | .nGram history len bound =>
      nGramCPSHistoryDecider { history, left := len, right := len, bound } M
  | .nGramLRU len bound =>
      nGramCPSLRUDecider { left := len, right := len, bound } M
  | .repWL len threshold maxT bound =>
      Deciders.RepWL.decider { len, threshold, maxT, bound } M
  | .halt bound =>
      haltDecider bound M
  | .loop1 bound =>
      Deciders.Loop1.decider bound M
  | .far states dfa =>
      Deciders.FAR.decider 5000001 { states, dfa := dfa.toArray } M
  | .wfar maxD leftStates left rightStates right bound =>
      Deciders.WFAR.decider {
        maxD
        left := { states := leftStates, trans := left.toArray }
        right := { states := rightStates, trans := right.toArray }
        bound
      } M
  | .sporadic =>
      .loops_prf (sporadic_nonHalting M)
  | .unsupported _ =>
      .unknown ()

def machineCode (M : Machine 4 1) : String :=
  toString (repr M)

def findEntry? (entries : List Entry) (M : Machine 4 1) : Option EntryDecider :=
  let code := machineCode M
  entries.findSome? fun entry =>
    if entry.fst = code then
      some entry.snd
    else
      none

def tableOfEntries (entries : List Entry) : Table :=
  Std.HashMap.ofList entries

def findInTable? (table : Table) (M : Machine 4 1) : Option EntryDecider :=
  table.get? (machineCode M)

def decider (entries : List Entry) (M : Machine 4 1) : HaltM M Unit :=
  match findEntry? entries M with
  | none => .unknown ()
  | some d => d.run M

def tableDecider (table : Table) (M : Machine 4 1) : HaltM M Unit :=
  match findInTable? table M with
  | none => .unknown ()
  | some d => d.run M

def emptyEntries : List Entry := []

def sporadicEntries : List Entry := [
  ("1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA", .sporadic),
  ("1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD", .sporadic),
  ("1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA", .sporadic),
  ("1RB1LA_0LC0RE_---1LD_1RA0LC_1RA1RE", .sporadic),
  ("1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE", .sporadic),
  ("1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC", .sporadic),
  ("1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB", .sporadic),
  ("1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC", .sporadic),
  ("1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA", .sporadic),
  ("1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---", .sporadic),
  ("1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE", .sporadic),
  ("1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA", .sporadic),
  ("1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA", .sporadic)
]

def initialEntries : List Entry :=
  sporadicEntries

def initialTable : Table :=
  tableOfEntries initialEntries

end Deciders.BB5Table
