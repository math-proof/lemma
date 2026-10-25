import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryHolderDerivative.Part3
open StatMech StatMech.Universality


/--
[fkIsingExpandingBoundarySquare_carrier_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_carrier_isCompact_eq
  {k : Nat} :
-- imply
  IsCompact (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_carrier_isCompact k

/--
[exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound_eq :
-- imply
  ∃ C : Nat → NNReal, ∀ k z, z ∈ convexHull Real (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) → ‖deriv (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) z‖₊ ≤ C k := by
-- proof
  apply StatMech.Universality.exists_fkIsingExpandingBoundarySquare_scaleDerivativeBound

/--
[exists_fkIsingExpandingBoundarySquare_scaleLipschitzBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma exists_fkIsingExpandingBoundarySquare_scaleLipschitzBound_eq :
-- imply
  ∃ C : Nat → NNReal, ∀ k, LipschitzOnWith (C k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) := by
-- proof
  apply StatMech.Universality.exists_fkIsingExpandingBoundarySquare_scaleLipschitzBound

/--
[lagrangeShrinkingTwoPointPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointPosition_injective_eq
  {k : Nat} :
-- imply
  Function.Injective (lagrangeShrinkingTwoPointPosition k) := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointPosition_injective k

/--
[lagrangeShrinkingTwoPointValue_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointValue_norm_le_one_eq
  {i : Fin 2} :
-- imply
  ‖lagrangeShrinkingTwoPointValue i‖ ≤ 1 := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointValue_norm_le_one i

/--
[lagrangeShrinkingTwoPointPosition_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointPosition_dist_eq
  {k : Nat} :
-- imply
  dist (lagrangeShrinkingTwoPointPosition k 0) (lagrangeShrinkingTwoPointPosition k 1) = 1 / (k + 1 : Nat) := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointPosition_dist k

/--
[lagrangeShrinkingTwoPointInterpolant_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointInterpolant_eq_eq
  {k : Nat}
  {z : Complex} :
-- imply
  finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k) lagrangeShrinkingTwoPointValue z = ((k + 1 : Nat) : Complex) * z := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointInterpolant_eq k z

/--
[lagrangeShrinkingTwoPointInterpolant_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointInterpolant_deriv_eq
  {k : Nat}
  {z : Complex} :
-- imply
  deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k) lagrangeShrinkingTwoPointValue) z = ((k + 1 : Nat) : Complex) := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointInterpolant_deriv k z

/--
[lagrangeShrinkingTwoPointPosition_zero_mem_convexHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPointPosition_zero_mem_convexHull_eq
  {k : Nat} :
-- imply
  (0 : Complex) ∈ convexHull Real (Set.range (lagrangeShrinkingTwoPointPosition k)) := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPointPosition_zero_mem_convexHull k

/--
[lagrangeShrinkingTwoPoint_no_uniform_derivative_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma lagrangeShrinkingTwoPoint_no_uniform_derivative_bound_eq :
-- imply
  ¬ ∃ C : NNReal, ∀ k z, z ∈ convexHull Real (Set.range (lagrangeShrinkingTwoPointPosition k)) → ‖deriv (finiteLagrangeInterpolant (lagrangeShrinkingTwoPointPosition k) lagrangeShrinkingTwoPointValue) z‖₊ ≤ C := by
-- proof
  apply StatMech.Universality.lagrangeShrinkingTwoPoint_no_uniform_derivative_bound

/--
[fkIsingExpandingBoundarySquare_entireSquarePrimitive_deriv_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_entireSquarePrimitive_deriv_medial_eq
  {k : Nat}
  {e : fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k} :
-- imply
  deriv (isingFermionicEntireSquarePrimitive (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k)) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.medialEmbedding k e) = (@FKIsingDobrushinDomain.normalizedFermionicObservable (fkIsingExpandingBoundarySquareCaratheodoryApproximation.P k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.decEqM k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.dobrushin k) (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k) e) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_entireSquarePrimitive_deriv_medial k e

/--
[fkIsingExpandingBoundarySquare_scalingLimit_of_deriv_and_dense_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryHolderDerivative.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_scalingLimit_of_deriv_and_dense_primitiveIm_eq
  {C : NNReal}
  {E : StatMech.FrontierA.CompactExhaustion fkIsingExpandingBoundarySquareCaratheodoryApproximation.U}
-- given
  (hderiv : forall k z, z ∈ convexHull Real (fkIsingExpandingBoundarySquareCaratheodoryApproximation.carrier k) -> ‖deriv (fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant k) z‖₊ ≤ C)
  (target Phi : Complex -> Complex)
  (htarget : DifferentiableOn Complex target fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (htarget_ne : target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z => target z ^ 2) fkIsingExpandingBoundarySquareCaratheodoryApproximation.U)
  (hidentifyDense : forall (phi psi : Nat -> Nat) (f : Complex -> Complex), StrictMono phi -> StrictMono psi -> TendstoLocallyUniformlyOn (fun k => fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant (phi (psi k))) f Filter.atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U -> exists (S : Set Complex) (C : Real), Dense S ∧ Set.EqOn (fun z => (isingFermionicEntireSquarePrimitive f z).im) (fun z => (Phi z).im + C) S ∧ f fkIsingExpandingBoundarySquareCaratheodoryApproximation.root = target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) :
-- imply
  TendstoLocallyUniformlyOn fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant target Filter.atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U ∧ TendstoLocallyUniformlyOn (deriv ∘ fkIsingExpandingBoundarySquareCaratheodoryApproximation.normalizedInterpolant) (deriv target) Filter.atTop fkIsingExpandingBoundarySquareCaratheodoryApproximation.U := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_scalingLimit_of_deriv_and_dense_primitiveIm C hderiv target Phi htarget htarget_ne hPhi hPhideriv E hidentifyDense


-- created on 2026-10-23
