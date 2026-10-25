/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/PolynomiallyRecursiveMCFinite.lean -/

import Def.NumberTheory.PRecursiveSequence
import Mathlib.Algebra.MvPolynomial.Eval
import Abbrev.Dynamics.EventuallyPeriodicSequence
import Lemma.Set.EventuallyPeriodicSequence
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic


namespace MetaMathlibExt

/-- An integer sequence `s` is MC-finite if for every modulus `m > 0` it eventually satisfies,
modulo `m`, a linear recurrence with constant integer coefficients: there are `p, q > 0` and
`c₀, …, c_{p-1}` with `s (n + p) ≡ ∑ i < p, cᵢ s (n + i) [ZMOD m]` for all `n ≥ q`.

Source: Filmus, Fischer, Makowsky, and Rakita, "MC-Finiteness of Restricted Set Partition
Functions," Journal of Integer Sequences 26 (2023), Article 23.7.4, lines 281–286. -/
def IsMCFinite (s : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      ∃ c : Fin p → ℤ, ∀ n : ℕ, q ≤ n →
        (s (n + p) - ∑ i : Fin p, c i * s (n + i.val)) % (↑m : ℤ) = 0

end MetaMathlibExt
