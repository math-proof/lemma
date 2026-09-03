import sympy.matrices.expressions.special
import sympy.tensor.functions


noncomputable def rotaryMatrix (θ : Tensor ℝ [d]) : Tensor ℝ [d + d, d + d] :=
  let I : Tensor ℝ [d, d] := Tensor.eye d
  (I * [_ < d] θ.cos).hstack (-(I * [_ < d] θ.sin)) ++ (I * [_ < d] θ.sin).hstack (I * [_ < d] θ.cos)


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  rotaryMatrix θ = (Tensor.eye d * [_ < d] θ.cos).hstack (-(Tensor.eye d * [_ < d] θ.sin)) ++ (Tensor.eye d * [_ < d] θ.sin).hstack (Tensor.eye d * [_ < d] θ.cos) :=
-- proof
  rfl


-- created on 2026-09-03
