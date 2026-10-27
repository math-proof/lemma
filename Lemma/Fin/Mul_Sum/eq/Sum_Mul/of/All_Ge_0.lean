import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[mul_finset_sum_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {c : EReal}
  {f : Fin n → EReal}
-- given
  (hf : ∀ i, 0 ≤ f i) :
-- imply
  c * (∑ i, f i) = ∑ i, c * f i :=
-- proof
  EReal.mul_finset_sum_of_nonneg n c f hf


-- created on 2026-10-20
