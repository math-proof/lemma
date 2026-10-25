import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
open StatMech StatMech.Universality StatMech.Universality.VertexWalkData


/--
[hexExpI_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexExpI_mul_eq
  {a b : ℝ} :
-- imply
  Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexExpI_mul a b

/--
[hexExpI_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexExpI_zpow_eq
  {a : ℝ}
  {k : ℤ} :
-- imply
  (Complex.exp ((a : ℂ) * Complex.I)) ^ k = Complex.exp ((((k : ℝ) * a : ℝ) : ℂ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexExpI_zpow a k

/--
[hexExpI_add_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexExpI_add_neg_eq
  {θ : ℝ} :
-- imply
  Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) = 2 * (Real.cos θ : ℂ) := by
-- proof
  apply StatMech.Universality.hexExpI_add_neg θ

/--
[hexOmega_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexOmega_sq_eq :
-- imply
  hexOmega ^ 2 = Complex.exp (((2 * (2 * Real.pi / 3) : ℝ) : ℂ) * Complex.I) := by
-- proof
  apply StatMech.Universality.hexOmega_sq

/--
[hexCos_pi8_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexCos_pi8_pos_eq :
-- imply
  0 < Real.cos (Real.pi / 8) := by
-- proof
  apply StatMech.Universality.hexCos_pi8_pos

/--
[hexChi_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexChi_pos_eq :
-- imply
  0 < hexChi := by
-- proof
  apply StatMech.Universality.hexChi_pos

/--
[hexChi_eq_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexChi_eq_sqrt_eq :
-- imply
  hexChi = 1 / Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexChi_eq_sqrt

/--
[hexPair_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexPair_zero_eq :
-- imply
  hexOmega * hexLambda ^ (-4 : ℤ) + hexOmega ^ 2 * hexLambda ^ (4 : ℤ) = 0 := by
-- proof
  apply StatMech.Universality.hexPair_zero

/--
[hexTriplet_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexTriplet_zero_eq :
-- imply
  (1 : ℂ) + (hexChi : ℂ) * (hexOmega * hexLambda ^ (-1 : ℤ)) + (hexChi : ℂ) * (hexOmega ^ 2 * hexLambda ^ (1 : ℤ)) = 0 := by
-- proof
  apply StatMech.Universality.hexTriplet_zero

/--
[hexPairContribution_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexPairContribution_zero_eq
  {du : ℂ}
  {k : ℤ}
  {n : ℕ} :
-- imply
  hexContribution (hexOmega * du) (k - 4) n + hexContribution (hexOmega ^ 2 * du) (k + 4) n = 0 := by
-- proof
  apply StatMech.Universality.hexPairContribution_zero du k n

/--
[hexTripletContribution_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma hexTripletContribution_zero_eq
  {du : ℂ}
  {k : ℤ}
  {n : ℕ} :
-- imply
  hexContribution du k n + hexContribution (hexOmega * du) (k - 1) (n + 1) + hexContribution (hexOmega ^ 2 * du) (k + 1) (n + 1) = 0 := by
-- proof
  apply StatMech.Universality.hexTripletContribution_zero du k n

/--
[relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean)
-/
@[path]
private lemma relation_eq
  {D : VertexWalkData} :
-- imply
  D.vertexSum = 0 := by
-- proof
  apply StatMech.Universality.VertexWalkData.relation D


-- created on 2026-10-23
