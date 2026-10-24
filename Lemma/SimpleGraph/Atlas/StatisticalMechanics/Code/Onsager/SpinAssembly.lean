import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SpinAssembly
open StatMech StatMech.Onsager


/--
[ons_spinKacWardIdentities_of_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean)
-/
@[path]
private lemma ons_spinKacWardIdentities_of_matrix_eq
  {beta : ℝ}
-- given
  (h : ons_spinKacWardMatrixIdentities beta) :
-- imply
  ons_spinKacWardIdentities beta := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardIdentities_of_matrix beta h

/--
[ons_spinKacWardMatrixIdentities_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean)
-/
@[path]
private lemma ons_spinKacWardMatrixIdentities_zero_eq :
-- imply
  ons_spinKacWardMatrixIdentities 0 := by
-- proof
  apply StatMech.Onsager.ons_spinKacWardMatrixIdentities_zero

/--
[ons_KacWardResidue_of_spinKacWard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean)
-/
@[path]
private lemma ons_KacWardResidue_of_spinKacWard_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hcrit : beta ≠ ons_betaC)
  (hspin : ons_spinKacWardIdentities beta) :
-- imply
  ons_KacWardResidue beta := by
-- proof
  apply StatMech.Onsager.ons_KacWardResidue_of_spinKacWard beta hbeta hcrit hspin

/--
[ons_KacWardResidue_of_spinKacWardMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinAssembly.lean)
-/
@[path]
private lemma ons_KacWardResidue_of_spinKacWardMatrix_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hcrit : beta ≠ ons_betaC)
  (hspin : ons_spinKacWardMatrixIdentities beta) :
-- imply
  ons_KacWardResidue beta := by
-- proof
  apply StatMech.Onsager.ons_KacWardResidue_of_spinKacWardMatrix beta hbeta hcrit hspin


-- created on 2026-10-23
