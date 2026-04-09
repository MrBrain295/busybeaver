import Busybeaver.TM.Model.ClosedSet

/-
Loopers are machines going through the same configuration twice.

It is enough to find a looping state, and to show that the machine reaches this state to show that the
machine loops

Note that because of the HaltM monad, execution of the machine can stop early with a halting certificate.
-/

namespace Deciders.Cyclers

open TM.Model

variable {M : Type _} [TM.Model M]

private structure RunnerState (m : M) (k b : ℕ) where
  cfg : TM.Model.Config M
  multistep : default -[m]{k}->' cfg
  multistepBase : default -[m]{b}->>' cfg

private def advance (m : M) (σ : RunnerState m k b) :
    TM.Model.HaltM m (Σ b', RunnerState m (k + 1) b') :=
  match hstep : TM.Model.step m σ.cfg with
  | ⟨dn, .halted _⟩ =>
      .halts_prf b σ.cfg <| by
        constructor
        · simp [TM.Model.LastState, hstep]
        · exact σ.multistepBase
  | ⟨dn, .continue nxt⟩ =>
      .unknown ⟨b + dn, {
        cfg := nxt
        multistep := by
          have hcontinue : TM.Model.Step m σ.cfg nxt := by
            simp [TM.Model.Step, hstep]
          simpa using TM.Model.Multistep.trans σ.multistep (TM.Model.Multistep.single hcontinue)
        multistepBase := by
          have hbase : TM.Model.StepBase m dn σ.cfg nxt := by
            simp [TM.Model.StepBase, hstep]
          simpa using TM.Model.MultistepBase.trans σ.multistepBase (TM.Model.MultistepBase.single hbase)
      }⟩

@[specialize bound]
def looperDecider (bound : ℕ) (m : M) : TM.Model.HaltM m Unit := Id.run do
  let rec looperDecInner (bound : ℕ)
      {ktort btort} (tort : RunnerState m ktort btort)
      {kheir bheir} (heir : RunnerState m kheir bheir)
      (hht : tort.cfg -[m]->*' heir.cfg) : TM.Model.HaltM m Unit := match bound with
    | 0 => .unknown ()
    | n + 1 => do
        let ⟨_, heir1⟩ ← advance m heir
        let ⟨_, nheir⟩ ← advance m heir1
        let ⟨_, ntort⟩ ← advance m tort
        if heq : nheir.cfg = ntort.cfg then
          .loops_prf (by
            suffices TM.Model.ClosedSet m (fun cfg => cfg = ntort.cfg) default by
              exact this.nonHalting
            constructor
            · intro A
              rcases A with ⟨A, hA⟩
              subst A
              have hTortNTort : tort.cfg -[m]{1}->' ntort.cfg := by
                simpa using TM.Model.Multistep.split_add tort.multistep ntort.multistep
              have hHeirNHeir : heir.cfg -[m]{2}->' nheir.cfg := by
                simpa [Nat.add_comm] using TM.Model.Multistep.split_add heir.multistep nheir.multistep
              obtain ⟨nth, hnth⟩ := TM.Model.Machine.EvStep.to_multistep hht
              have htortNTort : tort.cfg -[m]{nth + 2}->' ntort.cfg := by
                have : tort.cfg -[m]{nth + 2}->' nheir.cfg := by
                  simpa [Nat.add_assoc] using TM.Model.Multistep.trans hnth hHeirNHeir
                simpa [heq] using this
              have hCycle : ntort.cfg -[m]{nth + 1}->' ntort.cfg := by
                have htortNTort' : tort.cfg -[m]{1 + (nth + 1)}->' ntort.cfg := by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htortNTort
                simpa [Nat.add_assoc] using TM.Model.Multistep.split_add hTortNTort htortNTort'
              exact ⟨⟨ntort.cfg, rfl⟩, TM.Model.Progress.from_multistep hCycle⟩
            · exact ⟨⟨ntort.cfg, rfl⟩, TM.Model.Multistep.to_evstep ntort.multistep⟩)
        else
          looperDecInner n ntort nheir (by
            obtain ⟨nth, hnth⟩ := TM.Model.Machine.EvStep.to_multistep hht
            apply TM.Model.Multistep.to_evstep
            have hTortNTort : tort.cfg -[m]{1}->' ntort.cfg := by
              simpa using TM.Model.Multistep.split_add tort.multistep ntort.multistep
            have hHeirNHeir : heir.cfg -[m]{2}->' nheir.cfg := by
              simpa [Nat.add_comm] using TM.Model.Multistep.split_add heir.multistep nheir.multistep
            have hTortNHeir : tort.cfg -[m]{nth + 2}->' nheir.cfg := by
              simpa [Nat.add_assoc] using TM.Model.Multistep.trans hnth hHeirNHeir
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              TM.Model.Multistep.split_le hTortNHeir hTortNTort (by simp))
  looperDecInner bound
    { cfg := default, multistep := .refl, multistepBase := .refl }
    { cfg := default, multistep := .refl, multistepBase := .refl }
    .refl

end Deciders.Cyclers
