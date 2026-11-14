-- Carved from Lemma/Definitions/Def_Deformations_ContinuousSMulDiscrete.lean: instance decls only.
import Mathlib
import Class.Deformations_ContinuousSMulDiscrete
import Lemma.Filter.ContinuousSMulDiscrete

section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]


instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]


end
