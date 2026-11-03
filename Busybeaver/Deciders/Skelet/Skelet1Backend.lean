import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1

open TM.Table

/-- The proof supplied to the Skelet #1 table entry. -/
structure ProofBackend : Type where
  nonhalt : ¬ M.halts (default : Config 4 1)

end Deciders.Skelet.Skelet1
