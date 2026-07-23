import Lemma.Bool.SEqBFnS.of.SEq.SEq
import sympy.tensor.tensor
open Bool


@[main]
private lemma main
  [Add α]
  {A B : Tensor α s}
  {A' B' : Tensor α s'}
-- given
  (h_A : A ≃ A')
  (h_B : B ≃ B') :
-- imply
  A + B ≃ A' + B' :=
-- proof
  SEqBFnS.of.SEq.SEq h_A h_B (· + ·)


-- created on 2026-07-23
