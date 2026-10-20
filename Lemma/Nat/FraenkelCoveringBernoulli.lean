import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FraenkelCoveringBernoulli
open scoped BigOperators
open MetaMathlibExt


/--
[fraenkel_exact_M_cover_bernoulli_recurrence_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FraenkelCoveringBernoulli.lean)
-/
@[path]
private lemma fraenkel_exact_M_cover_bernoulli_recurrence_general_eq
  {q M m : ℕ}
  {a n : Fin q → ℕ}
-- given
  (hm : 1 ≤ m)
  (hn : ∀ i, 0 < n i)
  (ha : ∀ i, a i < n i)
  (hcover : ∀ k : ℤ, Int.indexedCoverMultiplicity n (fun i => ((a i : ℤ))) k = M) :
-- imply
  bernoulli m * ((M : ℚ) - ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1)) =
    ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
    (∑ s ∈ Finset.range m, bernoulli s * (Nat.choose m s : ℚ) *
    (((a i : ℚ)) / ((n i : ℚ))) ^ (m - s)) := by
-- proof
  apply MetaMathlibExt.fraenkel_exact_M_cover_bernoulli_recurrence_general q M m a n hm hn ha hcover

/--
[fraenkel_exact_M_cover_bernoulli_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FraenkelCoveringBernoulli.lean)
-/
@[path]
private lemma fraenkel_exact_M_cover_bernoulli_recurrence_eq
  {q M m : ℕ}
  {a n : Fin q → ℕ}
-- given
  (hq : 2 ≤ q)
  (hm : 1 ≤ m)
  (hn : ∀ i, 0 < n i)
  (ha : ∀ i, a i < n i)
  (hcover : ∀ k : ℤ, Int.indexedCoverMultiplicity n (fun i => ((a i : ℤ))) k = M) :
-- imply
  bernoulli m * ((M : ℚ) - ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1)) =
    ∑ i : Fin q, ((n i : ℚ)) ^ (m - 1) *
    (∑ s ∈ Finset.range m, bernoulli s * (Nat.choose m s : ℚ) *
    (((a i : ℚ)) / ((n i : ℚ))) ^ (m - s)) := by
-- proof
  apply MetaMathlibExt.fraenkel_exact_M_cover_bernoulli_recurrence q M m a n hq hm hn ha hcover


-- created on 2026-10-20
