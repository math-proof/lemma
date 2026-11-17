module

public import Mathlib
public import Theorem.Fin.RothDegreeBound.of.All_RothDegreeBound
public import Theorem.Fin.RothDegreeBoundOver_RothMvHasse.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothDegreeBound_RothHasseDetMul
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
