import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismAgreementKernelCauchy
open StatMech StatMech.FrontierA


/--
[oddPrismAgreementEndpointKernel_sq_le_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismAgreementKernelCauchy.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_sq_le_diagonal_eq
  {beta : Real}
  {n : Nat}
  {a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  oddPrismAgreementEndpointKernel beta n a q ^ 2 <= oddPrismAgreementEndpointKernel beta n a a * oddPrismAgreementEndpointKernel beta n q q := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_sq_le_diagonal beta n a q

/--
[oddPrismAgreementEndpointKernel_principalMinor_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismAgreementKernelCauchy.lean)
-/
@[path]
private lemma oddPrismAgreementEndpointKernel_principalMinor_nonneg_eq
  {beta : Real}
  {n : Nat}
  {a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))} :
-- imply
  0 <= oddPrismAgreementEndpointKernel beta n a a * oddPrismAgreementEndpointKernel beta n q q - oddPrismAgreementEndpointKernel beta n a q ^ 2 := by
-- proof
  apply StatMech.FrontierA.oddPrismAgreementEndpointKernel_principalMinor_nonneg beta n a q


-- created on 2026-10-23
