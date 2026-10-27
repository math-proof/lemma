import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitive.Part2
open Complex StatMech StatMech.Universality


/--
[isingPrimalProjectionDivergenceWithoutSouth_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutSouth_add_eq
  {north east south west : Complex} :
-- imply
  isingPrimalProjectionDivergenceWithoutSouth north east west + (Complex.normSq (isingProj Complex.I south) - Complex.normSq (isingProj 1 south)) = isingPrimalProjectionDivergence north east south west := by
-- proof
  apply StatMech.Universality.isingPrimalProjectionDivergenceWithoutSouth_add north east south west

/--
[isingPrimalPrimitiveLaplacian_eq_projectionDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalPrimitiveLaplacian_eq_projectionDivergence_eq
  {north east south west : Complex} :
-- imply
  isingPrimalPrimitiveLaplacian north east south west = isingPrimalProjectionDivergence north east south west := by
-- proof
  apply StatMech.Universality.isingPrimalPrimitiveLaplacian_eq_projectionDivergence north east south west

/--
[isingSquareSHolomorphicQuad_of_projection_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingSquareSHolomorphicQuad_of_projection_cycle_eq
  {north east south west : Complex}
-- given
  (hNE : isingProj 1 north = isingProj 1 east)
  (hES : isingProj Complex.I east = isingProj Complex.I south)
  (hSW : isingProj (-1) south = isingProj (-1) west)
  (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north) :
-- imply
  IsingSquareSHolomorphicQuad south west north east := by
-- proof
  apply StatMech.Universality.isingSquareSHolomorphicQuad_of_projection_cycle north east south west hNE hES hSW hWN

/--
[isingProj_normSq_add_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingProj_normSq_add_neg_eq
  {e f : Complex}
-- given
  (he : Complex.normSq e = 1) :
-- imply
  Complex.normSq (isingProj e f) + Complex.normSq (isingProj (-e) f) = Complex.normSq f := by
-- proof
  apply StatMech.Universality.isingProj_normSq_add_neg e f he

/--
[isingProj_normSq_le_two_mul_diagonal_variation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingProj_normSq_le_two_mul_diagonal_variation_eq
  {f : Complex} :
-- imply
  Complex.normSq f ≤ 2 * (|Complex.normSq (isingProj Complex.I f) - Complex.normSq (isingProj (-1) f)| + |Complex.normSq (isingProj 1 f) - Complex.normSq (isingProj Complex.I f)|) := by
-- proof
  apply StatMech.Universality.isingProj_normSq_le_two_mul_diagonal_variation f

/--
[isingPrimitiveIncrement_local_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimitiveIncrement_local_closed_eq
  {e u f : Complex}
-- given
  (he : Complex.normSq e = 1)
  (hu : Complex.normSq u = 1) :
-- imply
  isingPrimitiveIncrement (isingProj e f) - isingPrimitiveIncrement (isingProj u f) + isingPrimitiveIncrement (isingProj (-e) f) - isingPrimitiveIncrement (isingProj (-u) f) = 0 := by
-- proof
  apply StatMech.Universality.isingPrimitiveIncrement_local_closed e u f he hu

/--
[isingPrimitiveSquareCombination_eq_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimitiveSquareCombination_eq_normSq_eq
  {A B C D : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad A B C D) :
-- imply
  isingPrimitiveSquareCombination A B C D = (1 + Complex.I) * (Complex.normSq (A - C) : Complex) := by
-- proof
  apply StatMech.Universality.isingPrimitiveSquareCombination_eq_normSq A B C D h

/--
[isingPrimalPrimitiveLaplacian_eq_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalPrimitiveLaplacian_eq_normSq_eq
  {A B C D : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad A B C D) :
-- imply
  isingPrimalPrimitiveLaplacian A B C D = Complex.normSq (A - C) := by
-- proof
  apply StatMech.Universality.isingPrimalPrimitiveLaplacian_eq_normSq A B C D h

/--
[isingPrimalPrimitiveLaplacian_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalPrimitiveLaplacian_nonneg_eq
  {A B C D : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad A B C D) :
-- imply
  0 ≤ isingPrimalPrimitiveLaplacian A B C D := by
-- proof
  apply StatMech.Universality.isingPrimalPrimitiveLaplacian_nonneg A B C D h

/--
[isingPrimalPrimitiveLaplacian_rotate_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalPrimitiveLaplacian_rotate_two_eq
  {A B C D : Complex} :
-- imply
  isingPrimalPrimitiveLaplacian A B C D = -isingPrimalPrimitiveLaplacian C D A B := by
-- proof
  apply StatMech.Universality.isingPrimalPrimitiveLaplacian_rotate_two A B C D

/--
[isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad_eq
  {north east south west : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad south west north east) :
-- imply
  isingPrimalPrimitiveLaplacian north east south west ≤ 0 := by
-- proof
  apply StatMech.Universality.isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad north east south west h

/--
[isingPrimalProjectionDivergenceWithoutSouth_add_correction_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingPrimalProjectionDivergenceWithoutSouth_add_correction_nonpos_eq
  {north east south west : Complex}
  {c g : Real}
-- given
  (hquad : IsingSquareSHolomorphicQuad south west north east)
  (hcorr : c * g = Complex.normSq (isingProj Complex.I south) - Complex.normSq (isingProj 1 south)) :
-- imply
  isingPrimalProjectionDivergenceWithoutSouth north east west + c * g ≤ 0 := by
-- proof
  apply StatMech.Universality.isingPrimalProjectionDivergenceWithoutSouth_add_correction_nonpos north east south west c g hquad hcorr

/--
[isingDualPrimitiveLaplacian_eq_neg_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingDualPrimitiveLaplacian_eq_neg_normSq_eq
  {A B C D : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad A B C D) :
-- imply
  isingDualPrimitiveLaplacian A B C D = -Complex.normSq (A - C) := by
-- proof
  apply StatMech.Universality.isingDualPrimitiveLaplacian_eq_neg_normSq A B C D h

/--
[isingDualPrimitiveLaplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean)
-/
@[path]
private lemma isingDualPrimitiveLaplacian_nonpos_eq
  {A B C D : Complex}
-- given
  (h : IsingSquareSHolomorphicQuad A B C D) :
-- imply
  isingDualPrimitiveLaplacian A B C D ≤ 0 := by
-- proof
  apply StatMech.Universality.isingDualPrimitiveLaplacian_nonpos A B C D h


-- created on 2026-10-23
