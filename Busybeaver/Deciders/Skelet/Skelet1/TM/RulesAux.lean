import Busybeaver.Deciders.Skelet.Skelet1.TM.Lift

/-!
# Helpers for the machine-level rules

Conversions between configurations given by blocks and window states, so that
finite rules can be checked by running the window runner.
-/

namespace Sk1.TM.RulesAux

open Turing

theorem wreach_cfg {n : ℕ} {s t : W} (h : wreach n s t = true) (TL TR : ListBlank Bool)
    {c d : Cfg} (hc : s.den TL TR = c) (hd : t.den TL TR = d) : Reaches c d :=
  hc ▸ hd ▸ wreach_sound h TL TR

theorem empty_eq_blanks (k : ℕ) : (∅ : ListBlank Bool) = List.replicate k false +> ∅ := by
  have := append_blanks [] k
  simpa using this.symm

theorem den_st_appR (q : Q) (a b c : List Bool) (TL TR : ListBlank Bool) :
    (W.st q a b).den TL (c +> TR) = (W.st q a (b ++ c)).den TL TR := by
  simp only [W.den, append_append]

theorem den_st_appL (q : Q) (a b c : List Bool) (TL TR : ListBlank Bool) :
    (W.st q a b).den (c +> TL) TR = (W.st q (a ++ c) b).den TL TR := by
  simp only [W.den, append_append]

theorem den_exitL_app (q : Q) (b c : List Bool) (TL TR : ListBlank Bool) :
    (W.exitL q b).den TL (c +> TR) = (W.exitL q (b ++ c)).den TL TR := by
  simp only [W.den, append_append]

theorem dL_den (b : List Bool) (hb : b ≠ []) (L R : ListBlank Bool) :
    dL (b +> L) R = (W.st .C b.tail [b.head hb, true, false]).den L R := by
  cases b with
  | nil => exact absurd rfl hb
  | cons b0 bs => exact dL_cons_eq_den b0 bs L R

theorem dR_den (a b : List Bool) (L R : ListBlank Bool) :
    dR (a +> L) (b +> R) = (W.st .A a b).den L R := rfl

theorem dL_den' (b : List Bool) (L R : ListBlank Bool) :
    dL L (b +> R) = (W.exitL .C ([true, false] ++ b)).den L R :=
  dL_append_eq_exitL b L R

end Sk1.TM.RulesAux
