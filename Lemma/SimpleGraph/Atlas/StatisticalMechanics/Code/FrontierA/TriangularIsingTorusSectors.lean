import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
open StatMech StatMech.FrontierA


/--
[triangularTorusXSeamEdge_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma triangularTorusXSeamEdge_diagonal_eq
  {L : Nat}
  {y : ZMod L} :
-- imply
  triangularTorusXSeamEdge L s(((0 : ZMod L), y), (-1, y - 1)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusXSeamEdge_diagonal L y

/--
[triangularTorusYSeamEdge_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma triangularTorusYSeamEdge_diagonal_eq
  {L : Nat}
  {x : ZMod L} :
-- imply
  triangularTorusYSeamEdge L s((x, (0 : ZMod L)), (x - 1, -1)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusYSeamEdge_diagonal L x

/--
[two_mul_triangularTorusEvenSubgraphSum_eq_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma two_mul_triangularTorusEvenSubgraphSum_eq_spin_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real} :
-- imply
  (2 : Complex) * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight = triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 1 1 + triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 0 1 + triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 1 0 - triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 0 0 := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight

/--
[triangularTorusIsingPartition_highTemperature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_highTemperature_eq
  {L : Nat}
  [Fact (2 < L)]
  {coupling : Sym2 (ZMod L × ZMod L) → Real} :
-- imply
  StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset coupling (fun _ => 0) = (2 : Real) ^ Fintype.card (ZMod L × ZMod L) * (∏ edge ∈ (triangularTorusGraph L).edgeFinset, Real.cosh (coupling edge)) * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) (fun edge => Real.tanh (coupling edge)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_highTemperature L coupling

/--
[triangularTorusWeightedSpin_norm_le_evenSubgraphSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma triangularTorusWeightedSpin_norm_le_evenSubgraphSum_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real}
  {a b : Fin 2}
-- given
  (hweight : ∀ edge, 0 ≤ weight edge) :
-- imply
  ‖triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) a b‖ ≤ inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight := by
-- proof
  apply StatMech.FrontierA.triangularTorusWeightedSpin_norm_le_evenSubgraphSum L hweight a b

/--
[triangularTorusEvenSubgraphSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma triangularTorusEvenSubgraphSum_nonneg_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real}
-- given
  (hweight : ∀ edge, 0 ≤ weight edge) :
-- imply
  0 ≤ inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight := by
-- proof
  apply StatMech.FrontierA.triangularTorusEvenSubgraphSum_nonneg L hweight

/--
[two_mul_triangularTorusEvenSubgraphSum_le_sum_sector_norms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectors.lean)
-/
@[path]
private lemma two_mul_triangularTorusEvenSubgraphSum_le_sum_sector_norms_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real}
-- given
  (hweight : ∀ edge, 0 ≤ weight edge) :
-- imply
  2 * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight ≤ ‖triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 1 1‖ + ‖triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 0 1‖ + ‖triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 1 0‖ + ‖triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) 0 0‖ := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorusEvenSubgraphSum_le_sum_sector_norms L hweight


-- created on 2026-10-23
