-- Carved from Lemma/Definitions/Def_Deformations_ContinuousSMulDiscrete.lean: instance decls only.

module

public import Mathlib
public import Class.Deformations_ContinuousSMulDiscrete
public import Theorem.Filter.ContinuousSMulDiscrete

@[expose] public section

section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]


instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]


end
