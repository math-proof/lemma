import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part4
open Filter Metric Set Topology StatMech StatMech.FrontierA


/--
[holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion_eq
  {F : ℕ → ℂ → ℂ}
  {U : Set ℂ}
  {E : CompactExhaustion U}
-- given
  (hU : IsOpen U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C) :
-- imply
  IsLocallyUniformlySequentiallyPrecompact F U := by
-- proof
  apply StatMech.FrontierA.holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion F U hU hF hbounded E

/--
[rightHalfPlaneCompact_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma rightHalfPlaneCompact_isCompact_eq
  {n : ℕ} :
-- imply
  IsCompact (rightHalfPlaneCompact n) := by
-- proof
  apply StatMech.FrontierA.rightHalfPlaneCompact_isCompact n

/--
[rightHalfPlaneCompact_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma rightHalfPlaneCompact_subset_eq
  {n : ℕ} :
-- imply
  rightHalfPlaneCompact n ⊆ {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.rightHalfPlaneCompact_subset n

/--
[rightHalfPlaneCompact_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma rightHalfPlaneCompact_cofinal_eq
  {K : Set ℂ}
-- given
  (hK : IsCompact K)
  (hKU : K ⊆ {z : ℂ | 0 < z.re}) :
-- imply
  ∃ n, K ⊆ rightHalfPlaneCompact n := by
-- proof
  apply StatMech.FrontierA.rightHalfPlaneCompact_cofinal K hK hKU

/--
[leftHalfPlaneCompact_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leftHalfPlaneCompact_isCompact_eq
  {n : ℕ} :
-- imply
  IsCompact (leftHalfPlaneCompact n) := by
-- proof
  apply StatMech.FrontierA.leftHalfPlaneCompact_isCompact n

/--
[leftHalfPlaneCompact_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leftHalfPlaneCompact_subset_eq
  {n : ℕ} :
-- imply
  leftHalfPlaneCompact n ⊆ {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leftHalfPlaneCompact_subset n

/--
[leftHalfPlaneCompact_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leftHalfPlaneCompact_cofinal_eq
  {K : Set ℂ}
-- given
  (hK : IsCompact K)
  (hKU : K ⊆ {z : ℂ | z.re < 0}) :
-- imply
  ∃ n, K ⊆ leftHalfPlaneCompact n := by
-- proof
  apply StatMech.FrontierA.leftHalfPlaneCompact_cofinal K hK hKU

/--
[leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  IsLocallyUniformlySequentiallyPrecompact (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane d hbeta

/--
[leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta) :
-- imply
  IsLocallyUniformlySequentiallyPrecompact (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane d hbeta

/--
[leeYangBox_normalizedFieldLogDerivative_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_rightHalfPlane d hd hbeta

/--
[leeYangBox_normalizedFieldLogDerivative_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean)
-/
@[path]
private lemma leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  ∃ g : ℂ → ℂ, TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_normalizedFieldLogDerivative_leftHalfPlane d hd hbeta


-- created on 2026-10-23
