import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SumSquares.RepresentationCount
open SumSquares


/--
[mem_solutions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma mem_solutions_eq
  {k n : ℕ}
  {x : Fin k → ℤ} :
-- imply
  x ∈ solutions k n ↔ dotProduct x x = (n : ℤ) := by
-- proof
  apply SumSquares.mem_solutions

/--
[solutions_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma solutions_finite_eq
  {k n : ℕ} :
-- imply
  Set.Finite (solutions k n) := by
-- proof
  apply SumSquares.solutions_finite k n

/--
[representationNumber_eq_toFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma representationNumber_eq_toFinset_card_eq
  {k n : ℕ} :
-- imply
  representationNumber k n = (solutions_finite k n).toFinset.card := by
-- proof
  apply SumSquares.representationNumber_eq_toFinset_card k n

/--
[zero_mem_solutions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma zero_mem_solutions_eq
  {k : ℕ} :
-- imply
  (0 : Fin k → ℤ) ∈ solutions k 0 := by
-- proof
  apply SumSquares.zero_mem_solutions k

/--
[zero_notMem_solutions_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma zero_notMem_solutions_succ_eq
  {k n : ℕ} :
-- imply
  (0 : Fin k → ℤ) ∉ solutions k (n + 1) := by
-- proof
  apply SumSquares.zero_notMem_solutions_succ k n

/--
[neg_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma neg_mem_iff_eq
  {k n : ℕ}
  {x : Fin k → ℤ} :
-- imply
  (-x) ∈ solutions k n ↔ x ∈ solutions k n := by
-- proof
  apply SumSquares.neg_mem_iff

/--
[solutions_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma solutions_zero_zero_eq
  :
-- imply
  solutions 0 0 = Set.univ := by
-- proof
  apply SumSquares.solutions_zero_zero

/--
[solutions_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma solutions_zero_succ_eq
  {n : ℕ} :
-- imply
  solutions 0 (n + 1) = ∅ := by
-- proof
  apply SumSquares.solutions_zero_succ n

/--
[solutions_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma solutions_one_zero_eq
  :
-- imply
  solutions 1 0 = {(0 : Fin 1 → ℤ)} := by
-- proof
  apply SumSquares.solutions_one_zero

/--
[representationNumber_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma representationNumber_zero_zero_eq
  :
-- imply
  representationNumber 0 0 = 1 := by
-- proof
  apply SumSquares.representationNumber_zero_zero

/--
[representationNumber_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma representationNumber_zero_succ_eq
  {n : ℕ} :
-- imply
  representationNumber 0 (n + 1) = 0 := by
-- proof
  apply SumSquares.representationNumber_zero_succ n

/--
[representationNumber_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
private lemma representationNumber_one_zero_eq
  :
-- imply
  representationNumber 1 0 = 1 := by
-- proof
  apply SumSquares.representationNumber_one_zero


-- created on 2026-10-20
