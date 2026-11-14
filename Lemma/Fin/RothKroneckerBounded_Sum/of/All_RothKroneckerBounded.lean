import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKroneckerBounded_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m D : ℕ} [Field K]
  (s : Finset ι) (P : ι → MvPolynomial (Fin m) K)
-- given
  (hP : ∀ a ∈ s, rothKroneckerBounded D (P a)) :
-- imply
  rothKroneckerBounded D (∑ a ∈ s, P a) := by
-- proof
  intro i hi h
  by_contra hnot
  apply (MvPolynomial.mem_support_iff.mp hi)
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finsupp.notMem_support_iff.mp
  exact fun hia ↦ hnot (hP a ha i hia h)


-- updated on 2026-11-13
-- created on 2026-10-21
