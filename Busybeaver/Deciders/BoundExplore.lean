-- Rewrite in terms of TM.Model rather than TM.Machine
import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Model.Reachability

namespace TM.Table

/--
A decider that explores a bounded number of steps of the machine and produces a
certificate that the machine halts if it finds the end.

This is more a proof of concept that simple verifiers are possible rather that an
actual verifier.
-/
-- def boundedExplore [Inhabited $ Label l] [Inhabited $ Symbol s] (bound: ℕ): HaltM M Unit := do
--   let cur: { s // M.Reaches init s } := ⟨init, Machine.Reaches.refl⟩
--   .unknown ()
def boundedExplore (bound: ℕ) (M: Machine l s): HaltM M { s // default -[M]{bound}-> s } :=
  let rec boundedExploreCore (left: ℕ) {k} (hk: left + k = bound) (σ: { s // init -[M]{k}-> s }):
    HaltM M { s // default -[M]{bound}-> s } := match left with
  | 0 => .unknown ⟨σ.val, by {
    simp at hk
    cases hk
    exact σ.prop
  }⟩
  | n + 1 => M.stepH σ >>= boundedExploreCore n (by {
    rw [← hk, Nat.add_comm k, Nat.add_assoc]
  })
  boundedExploreCore bound (by rfl) ⟨init, Machine.Multistep.refl⟩

end TM.Table

namespace Deciders.BoundExplore

open TM.Model

variable {M : Type _} [TM.Model M]

private structure ExploreState (m : M) (k b : ℕ) where
  cfg : Config M
  multistep : default -[m]{k}->' cfg
  multistepBase : default -[m]{b}->>' cfg

def boundedExplore (bound : ℕ) (m : M) : HaltM m { s // default -[m]{bound}->' s } :=
    let rec boundedExploreCore (left : ℕ) {k b}
        (hk : left + k = bound) (σ : ExploreState m k b) :
        HaltM m { s // default -[m]{bound}->' s } := match left with
    | 0 => .unknown ⟨σ.cfg, by
        simp at hk
        cases hk
        exact σ.multistep⟩
    | n + 1 =>
        match hstep : TM.Model.step m σ.cfg with
        | ⟨dn, .halted _⟩ =>
            .halts_prf b σ.cfg <| by
              constructor
              · simp [TM.Model.LastState, hstep]
              · exact σ.multistepBase
        | ⟨dn, .continue nxt⟩ =>
            let σ' : ExploreState m (k + 1) (b + dn) := {
              cfg := nxt
              multistep := by
                have hcontinue : σ.cfg -[m]->' nxt := by
                  simp [Step, hstep]
                simpa using Multistep.trans σ.multistep (Multistep.single hcontinue)
              multistepBase := by
                have hbase : StepBase m dn σ.cfg nxt := by
                  simp [StepBase, hstep]
                simpa using MultistepBase.trans σ.multistepBase (MultistepBase.single hbase)
            }
            boundedExploreCore n (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk) σ'

    boundedExploreCore bound (by simp) {
      cfg := default
      multistep := Multistep.refl
      multistepBase := MultistepBase.refl
    }

end Deciders.BoundExplore
