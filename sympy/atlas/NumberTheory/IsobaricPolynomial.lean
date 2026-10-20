/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IsobaricPolynomial.lean -/

import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Isobaric polynomials

Formalizes the required definition clause for isobaric polynomials:
a polynomial `P_{k,n}(t_1, …, t_k)` over `ℤ` whose monomials are indexed by
`α ⊢ n`, i.e. `∑ j, j * α_j = n`.
-/

noncomputable section

namespace MetaMathlibExt

open scoped BigOperators

/-- Weighted isobaric sum `∑ j, (j + 1) * d j` of an exponent vector.

This is the condition `∑_{j=1}^k j α_j = n` from the source, with `Fin k`
indices shifted by one. Source statement: `jis_975c9f8263707d64d52bd0a3`. -/
abbrev isobaricWeight {k : ℕ} (d : Fin k →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin k ↦ j.val + 1) d

/-- An isobaric polynomial of isobaric degree `n`: a polynomial over `ℤ` in
`k` variables that is weighted homogeneous for the source weights `j + 1`.
This is a source-facing specialization of Mathlib's standard
`MvPolynomial.IsWeightedHomogeneous` predicate. Source statement:
`jis_975c9f8263707d64d52bd0a3`. -/
abbrev IsIsobaric {k : ℕ} (n : ℕ) (P : MvPolynomial (Fin k) ℤ) : Prop :=
  MvPolynomial.IsWeightedHomogeneous (fun j : Fin k ↦ j.val + 1) P n

end MetaMathlibExt
