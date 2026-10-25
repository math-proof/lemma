import Mathlib
import sympy.Basic
import Def.NumberTheory.SumSquares.RepresentationCount
open SumSquares


namespace SumSquares

/--
[mem_solutions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma mem_solutions
  {k n : ℕ}
  {x : Fin k → ℤ} :
-- imply
  x ∈ solutions k n ↔ dotProduct x x = (n : ℤ) :=
-- proof
  Iff.rfl

end SumSquares

namespace SumSquares

/--
[solutions_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma solutions_finite
  {k n : ℕ} :
-- imply
  Set.Finite (solutions k n) := by
-- proof
  apply (Set.Finite.pi fun _ => Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset
  intro x hx
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hsq : x i ^ 2 ≤ (n : ℤ) := by
    rw [← (mem_solutions.mp hx)]
    simpa only [dotProduct, pow_two] using
      Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j))
        (Finset.mem_univ i)
  have habs : |x i| ≤ (n : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.natAbs_le_self_sq (x i)).trans hsq
  exact abs_le.mp habs

end SumSquares

namespace SumSquares

/--
[representationNumber_eq_toFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma representationNumber_eq_toFinset_card
  {k n : ℕ} :
-- imply
  representationNumber k n = (solutions_finite k n).toFinset.card :=
-- proof
Set.ncard_eq_toFinset_card _ _

end SumSquares

namespace SumSquares

/--
[zero_mem_solutions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma zero_mem_solutions
  {k : ℕ} :
-- imply
  (0 : Fin k → ℤ) ∈ solutions k 0 := by
-- proof
  simp [mem_solutions, dotProduct]

end SumSquares

namespace SumSquares

/--
[zero_notMem_solutions_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma zero_notMem_solutions_succ
  {k n : ℕ} :
-- imply
  (0 : Fin k → ℤ) ∉ solutions k (n + 1) := by
-- proof
  simp only [mem_solutions]
  intro h
  have h0 : dotProduct (0 : Fin k → ℤ) (0 : Fin k → ℤ) = 0 := by
    simp [dotProduct]
  rw [h0] at h
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne h.symm

end SumSquares

namespace SumSquares

/--
[neg_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma neg_mem_iff
  {k n : ℕ}
  {x : Fin k → ℤ} :
-- imply
  (-x) ∈ solutions k n ↔ x ∈ solutions k n := by
-- proof
  simp [mem_solutions, neg_dotProduct, dotProduct_neg]

end SumSquares

namespace SumSquares

/--
[solutions_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma solutions_zero_zero
  :
-- imply
  solutions 0 0 = Set.univ := by
-- proof
  ext x
  simp [mem_solutions, dotProduct]

end SumSquares

namespace SumSquares

/--
[solutions_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma solutions_zero_succ
  {n : ℕ} :
-- imply
  solutions 0 (n + 1) = ∅ := by
-- proof
  ext x
  simp only [Set.mem_empty_iff_false, mem_solutions, iff_false]
  intro h
  have h0 : dotProduct x x = 0 := by
    simp [dotProduct]
  have heq : ((n + 1 : ℕ) : ℤ) = 0 := by
    calc ((n + 1 : ℕ) : ℤ) = dotProduct x x := h.symm
      _ = 0 := h0
  have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  exact hne heq

end SumSquares

namespace SumSquares

/--
[solutions_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma solutions_one_zero
  :
-- imply
  solutions 1 0 = {(0 : Fin 1 → ℤ)} := by
-- proof
  ext x
  simp only [mem_solutions, Set.mem_singleton_iff]
  have hDot : dotProduct x x = x (0 : Fin 1) * x 0 := by
    simp only [dotProduct]
    have hU : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    rw [hU, Finset.sum_singleton]
  rw [hDot]
  have hx : x = (0 : Fin 1 → ℤ) ↔ x (0 : Fin 1) = 0 := by
    constructor
    · intro h
      exact congr_fun h 0
    · intro h0
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi, h0, Pi.zero_apply]
  rw [hx]
  simp [mul_eq_zero]

end SumSquares

namespace SumSquares

/--
[representationNumber_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma representationNumber_zero_zero
  :
-- imply
  representationNumber 0 0 = 1 := by
-- proof
  simp [representationNumber, solutions_zero_zero, Set.ncard_univ]

end SumSquares

namespace SumSquares

/--
[representationNumber_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma representationNumber_zero_succ
  {n : ℕ} :
-- imply
  representationNumber 0 (n + 1) = 0 := by
-- proof
  simp [representationNumber, solutions_zero_succ]

end SumSquares

namespace SumSquares

/--
[representationNumber_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SumSquares/RepresentationCount.lean)
-/
@[path]
lemma representationNumber_one_zero
  :
-- imply
  representationNumber 1 0 = 1 := by
-- proof
  simp [representationNumber, solutions_one_zero]

end SumSquares


-- created on 2026-10-20
-- updated on 2026-10-23
