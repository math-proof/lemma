import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicExitAssembly
open StatMech StatMech.Universality


/--
[isingLeapfrogDiffusiveExitInputs_of_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicExitAssembly.lean)
-/
@[path]
private lemma isingLeapfrogDiffusiveExitInputs_of_pointwise_eq
  {A : Real}
-- given
  (hA : 0 <= A)
  (hpoint : forall (R rho : Nat) (p p' : IsingLeapfrogBox R), 0 < rho -> IsingLeapfrogInteriorMargin R rho p -> IsingLeapfrogInteriorMargin R rho p' -> IsingLeapfrogDiagonalAdjacent p p' -> forall q, |isingLeapfrogExitKernel R (rho * rho) p q - isingLeapfrogExitKernel R (rho * rho + 1) p' q| <= A / (rho : Real) ^ 2) :
-- imply
  IsingLeapfrogDiffusiveExitInputs A 152 := by
-- proof
  apply StatMech.Universality.isingLeapfrogDiffusiveExitInputs_of_pointwise A hA hpoint


-- created on 2026-10-23
