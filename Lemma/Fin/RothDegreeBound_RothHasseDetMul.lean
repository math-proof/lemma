import Mathlib
import Lemma.Fin.RothDegreeBound.of.All_RothDegreeBound
import Lemma.Fin.RothDegreeBoundOver_RothMvHasse.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ} {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (u v : Fin k → RothMvIndex m) :
-- imply
  rothDegreeBound (rothHasseDet P u v) (fun h ↦ k * r h) := by
-- proof
  apply RothDegreeBound.of.All_RothDegreeBound
  intro s t
  apply RothDegreeBoundOver_RothMvHasse.of.RothMvIndex hP (u s + v t)


-- created on 2026-10-21
