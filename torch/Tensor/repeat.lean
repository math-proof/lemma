import sympy.tensor.Basic
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
open Tensor List

/--
[torch.repeat_interleave](https://docs.pytorch.org/docs/stable/generated/torch.repeat_interleave.html)
[numpy.repeat](https://numpy.org/doc/stable/reference/generated/numpy.repeat.html)

given :

X : Tensor α [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉]

t' = X.repeat 3 4

t': Tensor α [s₀, s₁, s₂, s₃, s₄ * 3, s₅, s₆, s₇, s₈, s₉]

the following eqaulity holds:
∀ X : Fin 3,
  X[i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉] = t'[i₀, i₁, i₂, i₃, i₄ + s₄ * X, i₅, i₆, i₇, i₈, i₉]
-/
def Tensor.repeat (X : Tensor α s) (dim : Fin s.length) (n : ℕ) : Tensor α (s.set dim (n * s[dim])) :=
  ⟨cast (by simp [ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength dim.isLt]) ((X.data.splitAt dim).map (·.repeat n)).flatten⟩
