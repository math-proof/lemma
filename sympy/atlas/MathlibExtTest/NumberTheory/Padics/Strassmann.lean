/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Strassmann.lean -/


import Lemma.Nat.Padics.Strassmann

-- Strassmann's theorem makes the zero set of a nonzero five-adic power series finite.
example [Fact (Nat.Prime 5)] (b : ℕ → ℚ_[5])
    (hb : Filter.Tendsto b Filter.cofinite (nhds 0)) (hne : b ≠ 0) :
    {y : ℚ_[5] | ‖y‖ ≤ 1 ∧ ∑' m, b m * y ^ m = 0}.Finite :=
  Padic.strassmann 5 b hb hne
