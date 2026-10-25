import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part7
open StatMech StatMech.FrontierA


/--
[two_mul_triangularTorus_spinCharacter_eq_walsh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma two_mul_triangularTorus_spinCharacter_eq_walsh_eq
  {a b : Fin 2}
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  2 * ons_spinCharacter a b h = ∑ chi : Fin 2 × Fin 2, triangularTorusQuadraticWalshSign a b chi * triangularTorusLinearCharacter chi h := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorus_spinCharacter_eq_walsh a b h

/--
[two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real}
  {a b : Fin 2} :
-- imply
  (2 : Complex) * triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) a b = ∑ chi : Fin 2 × Fin 2, (triangularTorusQuadraticWalshSign a b chi : Complex) * triangularTorusWeightedLinearCharacterSum L weight chi := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh L weight a b

/--
[prod_triangularTorusSeamTwistSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma prod_triangularTorusSeamTwistSign_eq
  {L : Nat}
  {chi : Fin 2 × Fin 2}
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  (∏ edge ∈ F, triangularTorusSeamTwistSign L chi edge) = triangularTorusLinearCharacter chi (triangularTorusEvenHomology L F) := by
-- proof
  apply StatMech.FrontierA.prod_triangularTorusSeamTwistSign L chi F

/--
[triangularTorusXSeamEdge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusXSeamEdge_card_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  ((triangularTorusGraph L).edgeFinset.filter (triangularTorusXSeamEdge L)).card = 2 * L := by
-- proof
  apply StatMech.FrontierA.triangularTorusXSeamEdge_card L

/--
[triangularTorusYSeamEdge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusYSeamEdge_card_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  ((triangularTorusGraph L).edgeFinset.filter (triangularTorusYSeamEdge L)).card = 2 * L := by
-- proof
  apply StatMech.FrontierA.triangularTorusYSeamEdge_card L

/--
[triangularTorusSeamTwistSign_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSeamTwistSign_eq_one_or_neg_one_eq
  {L : Nat}
  {chi : Fin 2 × Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  triangularTorusSeamTwistSign L chi edge = 1 ∨ triangularTorusSeamTwistSign L chi edge = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge

/--
[abs_triangularTorusSeamTwistSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma abs_triangularTorusSeamTwistSign_eq
  {L : Nat}
  {chi : Fin 2 × Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  |triangularTorusSeamTwistSign L chi edge| = 1 := by
-- proof
  apply StatMech.FrontierA.abs_triangularTorusSeamTwistSign L chi edge

/--
[cosh_triangularTorusSeamTwistedCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma cosh_triangularTorusSeamTwistedCoupling_eq
  {L : Nat}
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  Real.cosh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) = Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
-- proof
  apply StatMech.FrontierA.cosh_triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge

/--
[tanh_triangularTorusSeamTwistedCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma tanh_triangularTorusSeamTwistedCoupling_eq
  {L : Nat}
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  Real.tanh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) = triangularTorusSeamTwistSign L chi edge * Real.tanh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
-- proof
  apply StatMech.FrontierA.tanh_triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge

/--
[tanh_triangularTorusRealEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma tanh_triangularTorusRealEdgeWeight_eq
  {L : Nat}
  {J1 J2 J3 : Real} :
-- imply
  (fun edge => Real.tanh (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) = triangularTorusRealEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) := by
-- proof
  apply StatMech.FrontierA.tanh_triangularTorusRealEdgeWeight L J1 J2 J3

/--
[inhomogeneousEvenSubgraphSum_seamTwist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma inhomogeneousEvenSubgraphSum_seamTwist_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  inhomogeneousEvenSubgraphSum (triangularTorusGraph L) (fun edge => triangularTorusSeamTwistSign L chi edge * weight edge) = triangularTorusWeightedLinearCharacterSum L weight chi := by
-- proof
  apply StatMech.FrontierA.inhomogeneousEvenSubgraphSum_seamTwist L weight chi

/--
[triangularTorusSeamTwistedPartition_highTemperature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSeamTwistedPartition_highTemperature_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) = (2 : Real) ^ (L * L) * (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) * triangularTorusWeightedLinearCharacterSum L (triangularTorusRealEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) chi := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamTwistedPartition_highTemperature L J1 J2 J3 chi

/--
[triangularTorusSeamTwistedPartition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSeamTwistedPartition_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) = (2 : Real) ^ (L * L) * triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamTwistedPartition_eq L J1 J2 J3 chi

/--
[triangularTorusNormalizedLinearSector_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedLinearSector_pos_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  0 < triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi

/--
[ZJ_log_coupling_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma ZJ_log_coupling_sub_abs_le_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J J' : Sym2 V → Real} :
-- imply
  |Real.log (StatMech.Sharpness.ZJ E J (fun _ => 0)) - Real.log (StatMech.Sharpness.ZJ E J' (fun _ => 0))| ≤ ∑ edge ∈ E, |J edge - J' edge| := by
-- proof
  apply StatMech.FrontierA.ZJ_log_coupling_sub_abs_le E J J'

/--
[abs_triangularTorusRealEdgeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma abs_triangularTorusRealEdgeWeight_le_eq
  {L : Nat}
  {J1 J2 J3 : Real}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  |triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤ |J1| + |J2| + |J3| := by
-- proof
  apply StatMech.FrontierA.abs_triangularTorusRealEdgeWeight_le L J1 J2 J3 edge

/--
[abs_triangularTorusSeamTwistedCoupling_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma abs_triangularTorusSeamTwistedCoupling_sub_le_eq
  {L : Nat}
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  |triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge - triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤ 2 * (|J1| + |J2| + |J3|) * ((if triangularTorusXSeamEdge L edge then 1 else 0) + (if triangularTorusYSeamEdge L edge then 1 else 0)) := by
-- proof
  apply StatMech.FrontierA.abs_triangularTorusSeamTwistedCoupling_sub_le L J1 J2 J3 chi edge

/--
[triangularTorusSeamTwistedPartition_log_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSeamTwistedPartition_log_sub_abs_le_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0)) - Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0))| ≤ 8 * (|J1| + |J2| + |J3|) * L := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamTwistedPartition_log_sub_abs_le L J1 J2 J3 chi

/--
[triangularTorusSeamTwistedCoupling_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSeamTwistedCoupling_zero_eq
  {L : Nat}
  {J1 J2 J3 : Real} :
-- imply
  triangularTorusSeamTwistedCoupling L J1 J2 J3 (0, 0) = triangularTorusRealEdgeWeight L J1 J2 J3 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamTwistedCoupling_zero L J1 J2 J3

/--
[triangularTorusNormalizedLinearSector_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedLinearSector_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) = (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) (triangularTorusRealEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedLinearSector_zero L J1 J2 J3

/--
[triangularTorusNormalizedLinearSector_log_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedLinearSector_log_sub_abs_le_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 chi) - Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0))| ≤ 8 * (|J1| + |J2| + |J3|) * L := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedLinearSector_log_sub_abs_le L J1 J2 J3 chi

/--
[triangularTorusNormalizedLinearSector_le_exp_boundary_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedLinearSector_le_exp_boundary_mul_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {chi : Fin 2 × Fin 2} :
-- imply
  triangularTorusNormalizedLinearSector L J1 J2 J3 chi ≤ Real.exp (8 * (|J1| + |J2| + |J3|) * L) * triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedLinearSector_le_exp_boundary_mul L J1 J2 J3 chi

/--
[two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {a b : Fin 2} :
-- imply
  (2 : Complex) * triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b = ∑ chi : Fin 2 × Fin 2, (triangularTorusQuadraticWalshSign a b chi : Complex) * triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh L J1 J2 J3 a b

/--
[norm_triangularTorusNormalizedQuadraticSector_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma norm_triangularTorusNormalizedQuadraticSector_le_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {a b : Fin 2} :
-- imply
  ‖triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b‖ ≤ 2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) * triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
-- proof
  apply StatMech.FrontierA.norm_triangularTorusNormalizedQuadraticSector_le L J1 J2 J3 a b

/--
[two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  ((2 * triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) : Real) : Complex) = triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 1 + triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 1 + triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 0 - triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 0 := by
-- proof
  apply StatMech.FrontierA.two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf L J1 J2 J3

/--
[triangularTorusNormalizedLinearSector_zero_le_two_mul_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedLinearSector_zero_le_two_mul_max_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) ≤ 2 * arfSectorNormMax (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedLinearSector_zero_le_two_mul_max L J1 J2 J3

/--
[arfSectorNormMax_normalizedQuadratic_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma arfSectorNormMax_normalizedQuadratic_le_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  arfSectorNormMax (triangularTorusNormalizedQuadraticSector L J1 J2 J3) ≤ 2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) * triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
-- proof
  apply StatMech.FrontierA.arfSectorNormMax_normalizedQuadratic_le L J1 J2 J3

/--
[triangularTorusSigned_normalized_log_gap_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSigned_normalized_log_gap_abs_le_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)) - Real.log (arfSectorNormMax (triangularTorusNormalizedQuadraticSector L J1 J2 J3))| ≤ 8 * (|J1| + |J2| + |J3|) * L + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSigned_normalized_log_gap_abs_le L J1 J2 J3

/--
[triangularTorusNormalizedEvenSequence_eq_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedEvenSequence_eq_linear_eq
  {J1 J2 J3 : Real}
  {n : Nat} :
-- imply
  triangularTorusNormalizedEvenSequence J1 J2 J3 n = let L := n + 3 letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩ triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedEvenSequence_eq_linear J1 J2 J3 n

/--
[triangularTorusNormalizedSectorMaxSequence_eq_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedSectorMaxSequence_eq_quadratic_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
  {n : Nat} :
-- imply
  triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n = let L := n + 3 letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩ arfSectorNormMax (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedSectorMaxSequence_eq_quadratic J1 J2 J3 rho n

/--
[triangularTorusSigned_normalizedSequence_log_gap_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSigned_normalizedSequence_log_gap_abs_le_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
  {n : Nat} :
-- imply
  |Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) - Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)| ≤ 8 * (|J1| + |J2| + |J3|) * (n + 3) + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSigned_normalizedSequence_log_gap_abs_le J1 J2 J3 rho n

/--
[triangularTorusSigned_normalized_log_gap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSigned_normalized_log_gap_tendsto_zero_eq
  {J1 J2 J3 : Real}
  {rho : Complex} :
-- imply
  Filter.Tendsto (fun n : Nat => (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) - Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSigned_normalized_log_gap_tendsto_zero J1 J2 J3 rho

/--
[triangularTorusSignedNormalizedEven_logDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusSignedNormalizedEven_logDensity_tendsto_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSignedNormalizedEven_logDensity_tendsto J1 J2 J3 rho hrho hpos

/--
[triangularTorusNormalizedEvenSequence_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedEvenSequence_pos_eq
  {J1 J2 J3 : Real}
  {n : Nat} :
-- imply
  0 < triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedEvenSequence_pos J1 J2 J3 n

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_signed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_signed_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_signed J1 J2 J3 rho hrho hpos

/--
[sum_abs_triangularTorusRealEdgeWeight_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma sum_abs_triangularTorusRealEdgeWeight_sub_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 K1 K2 K3 : Real} :
-- imply
  (∑ edge ∈ (triangularTorusGraph L).edgeFinset, |triangularTorusRealEdgeWeight L J1 J2 J3 edge - triangularTorusRealEdgeWeight L K1 K2 K3 edge|) = (L * L : Nat) * (|J1 - K1| + |J2 - K2| + |J3 - K3|) := by
-- proof
  apply StatMech.FrontierA.sum_abs_triangularTorusRealEdgeWeight_sub L J1 J2 J3 K1 K2 K3

/--
[triangularTorusIsingPartition_freeEnergy_ray_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_ray_lipschitz_eq
  {J b c : Real}
  {n : Nat} :
-- imply
  |(-Real.log (triangularTorusIsingPartitionSequence b b (b * J) n) / (n + 3 : Real) ^ 2) - (-Real.log (triangularTorusIsingPartitionSequence c c (c * J) n) / (n + 3 : Real) ^ 2)| ≤ (2 + |J|) * |b - c| := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_ray_lipschitz J b c n

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_critical_eq
  {beta J : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hbeta : 0 < beta)
  (hJ : -1 < J)
  (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence beta beta (beta * J) n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_critical rho hrho hbeta hJ hroot

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one_eq
  {beta J : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hbeta : 0 < beta)
  (hJ : -1 < J) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence beta beta (beta * J) n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one rho hrho hbeta hJ

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one_eq
  {beta J : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hbeta : 0 < beta)
  (hJ : J ≤ -1) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence beta beta (beta * J) n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one rho hrho hbeta hJ

/--
[triangularKacWardPhaseRoot_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularKacWardPhaseRoot_pow_four_eq :
-- imply
  triangularKacWardPhaseRoot ^ 4 = Complex.I := by
-- proof
  apply StatMech.FrontierA.triangularKacWardPhaseRoot_pow_four

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_ray_eq
  {beta J : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence beta beta (beta * J) n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_ray beta J hbeta


-- created on 2026-10-23
