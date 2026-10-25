-- Carved from Lemma/Definitions/Def_Valuation_CompletionAlgebra.lean: instance decls only.
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.UniformMulAction

set_option autoImplicit false

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

instance continuousConstSMul_withVal : ContinuousConstSMul K (WithVal v) :=
  ⟨fun a => continuous_const_mul (WithVal.toVal v a)⟩

instance uniformContinuousConstSMul_withVal : UniformContinuousConstSMul K (WithVal v) :=
  uniformContinuousConstSMul_of_continuousConstSMul K (WithVal v)

instance algebraCompletion : Algebra K v.Completion := inferInstance


end Valuation

end
