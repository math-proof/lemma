import sympy.tensor.Basic
import torch.Tensor.reshape
import Lemma.List.ProdInsertIdx.eq.Prod
open Tensor List

/--
[torch.unsqueeze](https://docs.pytorch.org/docs/stable/generated/torch.unsqueeze.html)

given :

X : Tensor α [s₀, s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉]

t' = X.unsqueeze 4

t': Tensor α [s₀, s₁, s₂, s₃, 1, s₄, s₅, s₆, s₇, s₈, s₉]

the following eqaulity holds:

X[i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉] = t'[i₀, i₁, i₂, i₃, 0, i₄, i₅, i₆, i₇, i₈, i₉]
-/
def Tensor.unsqueeze (X : Tensor α s) (dim : ℕ) : Tensor α (s.insertIdx dim 1) :=
  X.reshape (s.insertIdx dim 1) (by simp [Prod.eq.ProdInsertIdx s dim])
