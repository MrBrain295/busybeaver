import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Fast
import Busybeaver.Deciders.Skelet.Skelet1.Lazy.Certified
import Busybeaver.Deciders.Skelet.Skelet1.TM.Machine

/-!
# Event runs for the Skelet #1 simulator

An event is either a simple step, one tick, or an accelerated universal cycle.
The relation is shared by the certificate frame lemmas and the final machine
soundness argument.
-/

namespace Sk1

/-- One event of the symbolic simulator. -/
def Step {R : Type} (o : ROps R) (c c' : St R) : Prop :=
  ∃ e, ev o e c = some c'

theorem fast_simple_eq_simple {R : Type} (o : ROps R) (c : St R) :
    F.simple o c = simple o c := by
  cases c with
  | mk right l r =>
    cases right
    · cases l with
      | nil => simp [F.simple, simple, F.lStep, F.lSym, F.lEmpty, F.lF3] <;> rfl
      | cons s l =>
        cases s <;> simp [F.simple, simple, F.lStep, F.lSym, F.lEmpty, F.lF3]
        all_goals
          cases l with
          | nil => rfl
          | cons t l =>
            cases t with
            | x n => cases n <;> rfl
            | _ => rfl
    · cases hpop : o.pop r <;>
        simp [F.simple, simple, F.rItem, F.rEnd, F.rC, F.rP2, F.rPD3, hpop] <;> rfl

theorem fast_ev_eq_ev {R : Type} (o : ROps R) (e : Nat) (c : St R) :
    F.ev o e c = ev o e c := by
  cases e with
  | zero => simpa [F.ev, ev] using fast_simple_eq_simple o c
  | succ e =>
    cases e with
    | zero => rfl
    | succ e => rfl

/-- A finite (possibly empty) sequence of symbolic events. -/
abbrev Steps {R : Type} (o : ROps R) : St R → St R → Prop :=
  Relation.ReflTransGen (Step o)

theorem run64_steps {R : Type} (o : ROps R) {n code : Nat} {c c' : St R}
    (h : F.run64 o n code c = some c') : Steps o c c' := by
  induction n generalizing code c c' with
  | zero => simp only [F.run64] at h; cases h; exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [F.run64, F.step64] at h
    cases he : F.ev o (code % 4) c with
    | none => simp [he] at h
    | some d =>
      simp only [he] at h
      have he' : ev o (code % 4) c = some d := by
        rw [← fast_ev_eq_ev]
        exact he
      exact Relation.ReflTransGen.head ⟨code % 4, he'⟩ (ih h)

theorem runPacked_steps {R : Type} (o : ROps R) {gs : List (Nat × Nat)} {c c' : St R}
    (h : F.runPacked o gs c = some c') : Steps o c c' := by
  induction gs generalizing c with
  | nil => simp only [F.runPacked, Option.some.injEq] at h; subst c'; exact .refl
  | cons g gs ih =>
    simp only [F.runPacked] at h
    cases hr : F.run64 o g.1 g.2 c with
    | none => simp [hr] at h
    | some d =>
      simp only [hr] at h
      exact (run64_steps o hr).trans (ih h)

end Sk1
