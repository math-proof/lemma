import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricStability
open Filter Topology StatMech StatMech.FrontierD


/--
[abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : (m + 1) + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q)) :
-- imply
  |sixVertexOddPositiveHalfRootGap q j * sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤ 2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) * sixVertexOddPositiveHalfRootGap q j ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le hc hN hcount hopen hsol j

/--
[abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : (m + 1) + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) x) :
-- imply
  |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower hc hN hcount hopen hsol hlower hdensity j

/--
[sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {j k : Fin m}
-- given
  (hjk : j ≠ k) :
-- imply
  sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k = sixVertexSymmetricScatteringDerivative c (-q j) (-q k) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative hjk

/--
[sixVertexOddNegativeHalfRootPartition_cellGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexOddNegativeHalfRootPartition_cellGap_eq
  {m : Nat}
  {q : Fin m → Real}
  {k : Nat}
-- given
  (hm : 0 < m)
  (hk : k < m) :
-- imply
  sixVertexOddNegativeHalfRootPartition q hm (k + 1) - sixVertexOddNegativeHalfRootPartition q hm k = sixVertexOddPositiveHalfRootGap q ⟨m - 1 - k, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexOddNegativeHalfRootPartition_cellGap q hm k hk

/--
[abs_sixVertexOddPositiveHalfScatteringEndpointSum_sub_integral_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma abs_sixVertexOddPositiveHalfScatteringEndpointSum_sub_integral_le_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {mesh : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hmesh : ∀ k, sixVertexOddPositiveHalfRootGap q k ≤ mesh) :
-- imply
  |∑ k, sixVertexOddPositiveHalfRootGap q k * sixVertexSymmetricScatteringDerivative c (-q j) (-q k) - ∫ y in -q ⟨m - 1, by omega⟩..0, sixVertexSymmetricScatteringDerivative c (-q j) y| ≤ (sixVertexSymmetricScatteringLipschitzConstant c : Real) * mesh * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddPositiveHalfScatteringEndpointSum_sub_integral_le hc hm hopen hmesh j

/--
[intervalIntegral_sixVertexOddSymmetricScatteringDerivative_root_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexOddSymmetricScatteringDerivative_root_bounds_eq
  {c : Real}
  {m : Nat}
  {q : Fin m → Real}
  {j kmax : Fin m}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q)) :
-- imply
  0 ≤ ∫ y in -q kmax..0, sixVertexSymmetricScatteringDerivative c (-q j) y ∧ (∫ y in -q kmax..0, sixVertexSymmetricScatteringDerivative c (-q j) y) ≤ sixVertexSymmetricScatteringBoundaryBound c := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexOddSymmetricScatteringDerivative_root_bounds hc hopen j kmax

/--
[abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {mesh : Real}
  {j : Fin m}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hmesh : ∀ k, sixVertexOddPositiveHalfRootGap q k ≤ mesh) :
-- imply
  |(∑ k ∈ Finset.univ.erase j, sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) - ∫ y in -q ⟨m - 1, by omega⟩..0, sixVertexSymmetricScatteringDerivative c (-q j) y| ≤ ((2 * Real.pi) * (sixVertexSymmetricScatteringLipschitzConstant c : Real) + 2 * (sixVertexAnisotropyMagnitude c / (sixVertexAnisotropyMagnitude c - 1))) * mesh := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh hc hm hopen hmesh j

/--
[sixVertexOddSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
-- given
  (hc : 2 < c)
  (hgap : ∀ k, sixVertexOddPositiveHalfRootGap q k ≠ 0)
  (hdom : ∀ j, ∑ k ∈ Finset.univ.erase j, ‖sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k‖ < ‖sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j‖) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance hc q hgap hdom

/--
[sixVertexOddSymmetricBetheRootJacobian_injective_of_sourceBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_injective_of_sourceBounds_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {G : Fin m → Real}
  {eps M : Real}
-- given
  (hc : 2 < c)
  (hq : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (heps : 0 ≤ eps)
  (hM : 0 ≤ M)
  (hmargin : M + 2 * eps < 2 * Real.pi)
  (hdiag : ∀ j, |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ eps)
  (hoff : ∀ j, |(∑ k ∈ Finset.univ.erase j, sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j k) - G j| ≤ eps)
  (hG : ∀ j, 0 ≤ G j ∧ G j ≤ M) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_injective_of_sourceBounds hc q hq G eps M heps hM hmargin hdiag hoff hG

/--
[sixVertexOddSymmetricBetheRootJacobian_injective_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_injective_of_finiteDensityLower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcount : (m + 1) + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) x)
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower < 2 * Real.pi) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_injective_of_finiteDensityLower hc hm hN hcount hopen hsol hlower hdensity hmargin

/--
[sixVertexOddSymmetricBetheRootJacobian_injective_of_weightedDensityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexOddSymmetricBetheRootJacobian_injective_of_weightedDensityClose_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m → Real}
  {rho : Real → Real}
  {rhoLower eta : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcount : (m + 1) + m ≤ N)
  (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m) (sixVertexOddSymmetricLift m q))
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ x, rhoLower ≤ rho x)
  (heta : eta ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2)
  (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N ((m + 1) + m) (sixVertexOddSymmetricLift m q) x - rho x)| ≤ eta)
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < 2 * Real.pi) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricBetheRootJacobian_injective_of_weightedDensityClose hc hm hN hcount hopen hsol hrhoLower hrho heta hclose hmargin

/--
[sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean)
-/
@[path]
private lemma sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective_eq
  {a b : Real}
  {N m : Nat}
  {rho : C(Set.Icc a b × Real, Real)}
  {rhoLower outer : Real}
  {z : SixVertexBetheContinuationSpace a b N ((m + 1) + m)}
-- given
  (ha : 2 < a)
  (hm : 0 < m)
  (hN : 0 < N)
  (hhalf : 2 * ((m + 1) + m) ≤ N)
  (hcount : (m + 1) + m ≤ N)
  (hrhoLower : 0 < rhoLower)
  (hrho : ∀ (t : Set.Icc a b) x, rhoLower ≤ sixVertexContinuumDensityAt rho t x)
  (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude t.1 - 1) / sixVertexRootDensityScale t.1) / 2)
  (hmargin : ∀ t : Set.Icc a b, sixVertexSymmetricScatteringBoundaryBound t.1 + 2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1 N (rhoLower / 2) < 2 * Real.pi)
  (hgauge : sixVertexContinuationWeightedFiniteDensityGauge ha N ((m + 1) + m) rho z < outer) :
-- imply
  Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m z.1.1 (sixVertexOddPositiveHalfProjection m z.1.2)) := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuationWeightedFiniteDensityGauge_oddJacobianInjective ha hm hN hhalf hcount rho hrhoLower hrho houter hmargin z hgauge


-- created on 2026-10-23
