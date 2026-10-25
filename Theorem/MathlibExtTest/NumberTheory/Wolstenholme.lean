/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Wolstenholme.lean -/


import Lemma.Nat.Wolstenholme
open scoped BigOperators


-- Exact-signature API check for Wolstenholme's theorem.
example (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    ∑ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 2))⁻¹) = 0 :=
  MathlibExt.NumberTheory.Wolstenholme.wolstenholme p hp h5

-- Small invocation at `p = 5`.
example : ∑ k ∈ Finset.Ico (1 : ℕ) 5, ((k : ZMod (5 ^ 2))⁻¹) = 0 :=
  MathlibExt.NumberTheory.Wolstenholme.wolstenholme 5 (by decide) (by decide)

