import BBTheorems.Common

/-- # BB(4,2) = 107 -/

open TM TM.Table Pipeline

namespace BBTheorems

theorem bb4_spec : ResultSpec 3 1 106 (toTableDeciderCore bb4DefaultConfig) := by
  decide

/-- `BB(4,2)` in the library convention (steps to the pre-halt configuration). -/
theorem bb4 : Busybeaver 3 1 = 106 := bb4_spec.busybeaver three_ne_zero

/-- `BB(4,2) = 107` in the literature convention (the halting transition counts). -/
theorem bb4_literature : Busybeaver 3 1 + 1 = 107 := by rw [bb4]

end BBTheorems
