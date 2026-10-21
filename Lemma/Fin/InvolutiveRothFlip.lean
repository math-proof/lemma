import Mathlib
import Lemma.Fin.GetRothFlip.eq.Sub.of.RothBox
import Lemma.Fin.EqRothFlip.of.RothBox.Ne
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothFlip_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (h : Fin m) :
-- imply
  Function.Involutive (rothFlip r h) := by
-- proof
  intro j
  funext k
  if hkh : k = h then
    subst k
    apply Fin.ext
    rw [GetRothFlip.eq.Sub.of.RothBox, GetRothFlip.eq.Sub.of.RothBox]
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  else
    rw [EqRothFlip.of.RothBox.Ne hkh, EqRothFlip.of.RothBox.Ne hkh]


-- created on 2026-10-21
