import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.UniformMulAction

set_option autoImplicit false

noncomputable section

namespace Valuation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)


@[simp] theorem algebraMap_completion_apply (a : K) : algebraMap K v.Completion a = (a : v.Completion) := rfl

theorem smul_completion_def (a : K) (x : v.Completion) : a • x = (a : v.Completion) * x :=
  Algebra.smul_def a x

example : (Algebra.toSMul : SMul K v.Completion) = UniformSpace.Completion.instSMul K (WithVal v) := rfl

end Valuation

end
