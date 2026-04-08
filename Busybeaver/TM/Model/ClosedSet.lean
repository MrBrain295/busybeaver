import Busybeaver.Basic
import Busybeaver.TM.Model.Reachability

namespace TM.Model

variable {M : Type _} [TM.Model M]

structure ClosedSet (m : M) (base: Config M → Prop) (I: Config M) where
  closed : ∀ (a: {S // base S}), ∃ (b: {S // base S}), a -[m]->+' b
  enters : ∃ (N: {S // base S}), I -[m]->*' N

namespace ClosedSet

end ClosedSet

end TM.Model
