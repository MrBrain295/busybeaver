import Busybeaver.Deciders.Skelet.Skelet1.Cert.Steps
import Busybeaver.Deciders.Skelet.Skelet1.TM.Het

/-! # One universal cycle as a run of simple steps and ticks (simulator level) -/

namespace Sk1

/-- Simple steps and single ticks of the eager simulator, on configurations without the
tail marker. -/
def Step0 (c c' : St (List RI)) : Prop :=
  simple eagerOps c = some c' ∨ tickSt eagerOps c = some c'

namespace UniCycleRun

open Het

/-- Start of the universal cycle: the leading run is `M + uniP` with `M = m + 1`. -/
def hc0 : HC := ⟨true, .D :: .C1 :: .x ⟨true, uniP⟩ :: Jc.map liftLS, []⟩

/-- End of the universal cycle. -/
def hcF : HC :=
  ⟨true, .D :: .C1 :: .x ⟨true, 0⟩ :: Jc.map liftLS ++ [.x (.pure 10344), .D, .x (.pure 7640), .C2],
    [.x (.pure 300), .D, .x (.pure 30826), .D, .x (.pure 72142), .D, .x (.pure 3076), .D,
      .x (.pure 1538), .D]⟩

/-- The universal cycle as a het run of 1087 events (190 ticks), checked by the kernel; the
deferred ticks received by the abstract right tail add up to `uniT`. -/
theorem run_ok : hrun 1087 hc0 = some (hcF, uniT) := by decide +kernel

end UniCycleRun

open Het UniCycleRun in
/-- **One universal cycle.**  For every `m`, every left tail `l` and every right tape `r`
that admits `uniT` ticks, the universal cycle is a run of simple steps and ticks.  It
consumes `uniP` from the leading `x`-run, puts one `F` block
`x 10344, D, x 7640, C2` on the left and one expanded `G` block on the right, and applies
`uniT` ticks to `r`. -/
theorem uni_cycle_steps (m : Nat) (l : List LS) {r r' : List RI}
    (h : sweep 0 uniT r = some r') :
    Relation.ReflTransGen Step0
      ⟨true, .D :: .C1 :: .x (m + uniP + 1) :: Jc ++ l, r⟩
      ⟨true, .D :: .C1 :: .x (m + 1) :: Jc ++ ([.x 10344, .D, .x 7640, .C2] ++ l),
        [.x 300, .D, .x 30826, .D, .x 72142, .D, .x 3076, .D, .x 1538, .D] ++ r'⟩ := by
  have hsw : sw uniT r = some r' := by
    have : uniT ≠ 0 := by decide
    simp [sw, this, h]
  have hrun := hrun_sound (M := m + 1) (by omega) l 1087 _ _ _ run_ok hsw
  have e0 : hc0.den (m + 1) l r = ⟨true, .D :: .C1 :: .x (m + uniP + 1) :: Jc ++ l, r⟩ := by
    simp only [HC.den, hc0, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      map_den_liftLS jc_tl_free, HL.den_x, HN.den_mk, ↓reduceIte]
    simp [HL.den, Nat.add_right_comm]
  have eF : hcF.den (m + 1) l r' =
      ⟨true, .D :: .C1 :: .x (m + 1) :: Jc ++ ([.x 10344, .D, .x 7640, .C2] ++ l),
        [.x 300, .D, .x 30826, .D, .x 72142, .D, .x 3076, .D, .x 1538, .D] ++ r'⟩ := by
    simp only [HC.den, hcF, List.map_cons, List.map_nil, List.cons_append, List.map_append,
      map_den_liftLS jc_tl_free, HL.den_x, HN.den_mk, HN.den_pure, ↓reduceIte]
    simp [HL.den, HN.pure, HN.den]
  rw [e0, eF] at hrun
  exact hrun

end Sk1
