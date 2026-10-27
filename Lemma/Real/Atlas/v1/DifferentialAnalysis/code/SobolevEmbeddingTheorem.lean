import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbeddingTheorem
open MeasureTheory Filter Topology SobolevEmbedding
open scoped ZeroAtInfty


namespace SobolevEmbedding

/--
[sobolevEmbeddingThm_toFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean)
-/
@[path]
lemma sobolevEmbeddingThm_toFun
  {n m k : ℕ}
  {u : SobolevSpace n m}
-- given
  (hkm : k ≤ m)
  (hm : n < 2 * (m - k)) :
-- imply
  ⇑(sobolevEmbeddingThm hkm hm u).toZeroAtInftyContinuousMap = u.toFun :=
-- proof
  rfl
end SobolevEmbedding


/--
[sobolevSpace_toFun_continuous'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean)
-/
@[path]
private lemma sobolevSpace_toFun_continuous'_eq
  {n m : ℕ}
  {u : SobolevSpace n m}
-- given
  (hm : n < 2 * m) :
-- imply
  Continuous u.toFun := by
-- proof
  apply SobolevEmbedding.sobolevSpace_toFun_continuous' hm u

/--
[sobolevSpace_toFun_zeroAtInfty'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean)
-/
@[path]
private lemma sobolevSpace_toFun_zeroAtInfty'_eq
  {n m : ℕ}
  {u : SobolevSpace n m}
-- given
  (hm : n < 2 * m) :
-- imply
  Tendsto u.toFun (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
-- proof
  apply SobolevEmbedding.sobolevSpace_toFun_zeroAtInfty' hm u

/--
[sobolevSpace_contDiff'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean)
-/
@[path]
private lemma sobolevSpace_contDiff'_eq
  {n m k : ℕ}
  {u : SobolevSpace n m}
-- given
  (hkm : k ≤ m)
  (hm : n < 2 * (m - k)) :
-- imply
  ContDiff ℝ (k : ℕ∞) u.toFun := by
-- proof
  apply SobolevEmbedding.sobolevSpace_contDiff' hkm hm u

/--
[sobolevSpace_iteratedFDeriv_norm_tendsto_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbeddingTheorem.lean)
-/
@[path]
private lemma sobolevSpace_iteratedFDeriv_norm_tendsto_zero'_eq
  {n m : ℕ}
  {u : SobolevSpace n m}
  {j : ℕ}
-- given
  (hj : j ≤ m)
  (hm : n < 2 * (m - j)) :
-- imply
  Tendsto (fun x : EuclideanSpace ℝ (Fin n) => ‖iteratedFDeriv ℝ j u.toFun x‖) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
-- proof
  apply SobolevEmbedding.sobolevSpace_iteratedFDeriv_norm_tendsto_zero' u j hj hm


-- created on 2026-10-23
