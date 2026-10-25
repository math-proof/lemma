import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.MultiplicativeConvolution
open Nat Finset MultiplicativeConvolution


namespace MultiplicativeConvolution

/--
[mulConv_eq_arithmeticFunction_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultiplicativeConvolution.lean)
-/
@[path]
lemma mulConv_eq_arithmeticFunction_mul
  {f g : ArithmeticFunction ℂ}
  {n : ℕ} :
-- imply
  mulConv (fun n => f n) (fun n => g n) n = (f * g) n := by
-- proof
  simp [mulConv, ArithmeticFunction.mul_apply]

end MultiplicativeConvolution


-- created on 2026-10-23
