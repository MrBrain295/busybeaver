import Busybeaver.Deciders.NGramCPS.ClosedSetProof

open TM.Table

def nGramCPSDecider (cfg : NGramCPSConfig) (M : Machine l s) : HaltM M Unit :=
  if hcfg : cfg.n = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.runSearch M cfg.bound (NGramCPS.initialState cfg) with
    | .closed _ => .loops_prf (NGramCPS.closedResult_gives_closedSet cfg hcfg hSearch).nonHalting
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()

private theorem nGramCPSHistoryClosed_nonHalting
    (cfg : NGramCPSHistoryConfig) (M : Machine l s)
    (hSearch : NGramCPS.Generic.runHistory cfg M = .closed state) :
    ¬M.halts init := by
  sorry

def nGramCPSHistoryDecider (cfg : NGramCPSHistoryConfig) (M : Machine l s) : HaltM M Unit :=
  if cfg.left = 0 || cfg.right = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.Generic.runHistory cfg M with
    | .closed _ => .loops_prf (nGramCPSHistoryClosed_nonHalting cfg M hSearch)
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()
