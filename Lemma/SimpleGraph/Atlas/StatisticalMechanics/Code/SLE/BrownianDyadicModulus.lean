import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.BrownianDyadicModulus
open Filter MeasureTheory Set StatMech StatMech.SLE


/--
[brownianContinuousModification_ae_dyadicModulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicModulus.lean)
-/
@[path]
private lemma brownianContinuousModification_ae_dyadicModulus_eq :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, ∀ N : Nat, ∃ n0 : Nat, ∀ n, n0 <= n -> ∀ s ∈ Icc (-(N : Real)) N, ∀ t ∈ Icc (-(N : Real)) N, dist s t < ((brownianDyadicDenominator n : Nat) : Real)⁻¹ -> edist (brownianContinuousModification s omega) (brownianContinuousModification t omega) <= (513 : ENNReal) * brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.brownianContinuousModification_ae_dyadicModulus


-- created on 2026-10-23
