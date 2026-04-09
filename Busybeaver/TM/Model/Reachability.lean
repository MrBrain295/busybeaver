import Busybeaver.Basic

namespace TM.Model

variable {M : Type _} [TM.Model M]

-- Stepping with machine M from A leads to B in one step (not base steps)
def Step (m : M) (A B : Config M) : Prop :=
  (TM.Model.step m A |>.outcome) = .continue B

-- TODO: Remove the tick from this macro once we delete the old version.
notation (priority:=high) s₁ "-["m"]->'" s₂ => Step m s₁ s₂

inductive Multistep (m : M) : Nat → Config M → Config M → Prop
| refl {C} : Multistep m 0 C C
| step {A B C n} : (A -[m]->' B) → Multistep m n B C → Multistep m (n+1) A C

notation (priority:=high) s₁ "-["M"]{"k"}->'" s₂ => Multistep M k s₁ s₂

inductive Progress (m : M) : Config M → Config M → Prop
| single {C C'} : (C -[m]->' C') → Progress m C C'
| step {A B C} : (A -[m]->' B) → Progress m B C → Progress m A C

notation A " -[" m "]->+' " B => Progress m A B

inductive Machine.EvStep (m : M): Config M → Config M → Prop
| refl {C} : Machine.EvStep m C C
| step {A B C} : (A -[m]->' B) → Machine.EvStep m B C → Machine.EvStep m  A C

notation A " -["m"]->*' " B => Machine.EvStep m A B


def StepBase (m : M) (k : ℕ) (A B : Config M) : Prop :=
  (TM.Model.step m A) = ⟨k, .continue B⟩

-- `Base` talks about the base machine, so MultistepBase counts the number of steps taken by that machine,
-- rather than the high-level machine M.
inductive MultistepBase (m : M) : Nat → Config M → Config M → Prop
| refl {C} : MultistepBase m 0 C C
| step {A B C n₁ n₂} : StepBase m n₁ A B → MultistepBase m n₂ B C → MultistepBase m (n₁ + n₂) A C

notation (priority:=high) s₁ "-["m"]{"k"}->>'" s₂ => MultistepBase m k s₁ s₂

namespace Multistep

lemma single {m : M} (hAB : A -[m]->' B) : A -[m]{1}->' B :=
  .step hAB .refl

lemma trans {m : M} (hAB : A -[m]{i}->' B) (hBC : B -[m]{j}->' C) :
    A -[m]{i + j}->' C := by
  induction hAB with
  | refl =>
      simpa using hBC
  | step hAB hBD IH =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Multistep.step hAB (IH hBC)

lemma step_to_base {m : M} (hAB : A -[m]->' B) : ∃ n, StepBase m n A B := by
  cases hstep : TM.Model.step m A with
  | mk n outcome =>
      refine ⟨n, ?_⟩
      unfold Step at hAB
      unfold StepBase
      simpa [hstep] using hAB

lemma to_base {m : M} (hAB : A -[m]{i}->' B) : ∃ n, A -[m]{n}->>' B := by
  induction hAB with
  | refl =>
      exact ⟨0, .refl⟩
  | step hAB hBC IH =>
      obtain ⟨n₁, hn₁⟩ := step_to_base hAB
      obtain ⟨n₂, hn₂⟩ := IH
      exact ⟨n₁ + n₂, MultistepBase.step hn₁ hn₂⟩

end Multistep

namespace MultistepBase

lemma single {m : M} (hAB : StepBase m n A B) : A -[m]{n}->>' B :=
  .step hAB .refl

lemma trans {m : M} (hAB : A -[m]{i}->>' B) (hBC : B -[m]{j}->>' C) :
    A -[m]{i + j}->>' C := by
  induction hAB with
  | refl =>
      simpa using hBC
  | step hAB hBD IH =>
      simpa [Nat.add_assoc] using MultistepBase.step hAB (IH hBC)

end MultistepBase

def halts_in_base (m : M) (k : Nat) (A : Config M) : Prop := ∃ C, LastState m C ∧ A -[m]{k}->' C

def halts (m : M) (A : Config M) : Prop := ∃ k, halts_in_base m k A

inductive HaltM (m : M) (α : Type _)
| unknown : α → HaltM m α
| halts_prf n C : LastState m C ∧ (default -[m]{n}->>' C) → HaltM m α
| loops_prf : ¬halts m default → HaltM m α

namespace HaltM

variable {m : M} {α : Type _}

instance (m : M) : Monad (HaltM m) where
  pure := .unknown
  bind := fun x f =>
    match x with
    | .unknown v => f v
    | .halts_prf k C h => .halts_prf k C h
    | .loops_prf h => .loops_prf h

def decided : HaltM m α → Bool
| .unknown _ => false
| _ => true

end HaltM

noncomputable def stepH (m : M) (σ : {s // default -[m]{k}->' s}) :
    HaltM m {s' // default -[m]{k + 1}->' s'} :=
  match hstep : TM.Model.step m σ.val with
  | ⟨_, .halted _⟩ =>
      let n := Classical.choose (Multistep.to_base σ.prop)
      .halts_prf n σ.val <| by
        constructor
        · simp [TM.Model.LastState, hstep]
        · exact Classical.choose_spec (Multistep.to_base σ.prop)
  | ⟨_, .continue nxt⟩ =>
      .unknown ⟨nxt, by
        have hcontinue : σ.val -[m]->' nxt := by
          simp [Step, hstep]
        simpa using Multistep.trans σ.prop (Multistep.single hcontinue)⟩

end TM.Model
