import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.Correspondence
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Int


/--
[AlgebraicCurve_Place_one_le_ramificationIndexAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_one_le_ramificationIndexAlong.lean)
-/

private lemma AlgebraicCurve.Place.solution_impl
  [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F']
  (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
  (w : AlgebraicCurve.Place K F') :
  1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by
  let := AlgebraicCurve.algebraAlong φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  {φ : F →ₐ[K] F'}
  {w : AlgebraicCurve.Place K F'}
-- given
  (hφ : φ.toRingHom.IsIntegral) :
-- imply
  1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w :=
-- proof
  AlgebraicCurve.Place.solution_impl φ hφ w


-- created on 2026-10-24
