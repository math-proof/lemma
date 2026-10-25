import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
open SpernerProperty YoungLattice YoungLattice.Lmn


namespace YoungLattice.Lmn

/--
[complement_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
lemma complement_complement
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  p.complement.complement = p := by
-- proof
  apply ext; intro i
  show (complement (complement p)).val i = p.val i
  simp only [complement, Fin.rev_rev]
  apply Fin.ext; simp only []
  have := (p.val i).isLt; omega

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[complement_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
lemma complement_injective
  {m n : ℕ} :
-- imply
  Function.Injective (complement (m := m) (n := n)) := by
-- proof
  intro p q h
  have := congr_arg complement h
  rwa [complement_complement, complement_complement] at this

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[grade_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
lemma grade_complement
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  grade ℕ p.complement = m * n - grade ℕ p := by
-- proof
  rw [grade_eq, grade_eq]; have := sumParts_complement_add p; omega

end YoungLattice.Lmn

namespace YoungLattice.Lmn

/--
[Lmn_isRankSymmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
lemma Lmn_isRankSymmetric
  {m n : ℕ} :
-- imply
  IsRankSymmetric (α := Lmn m n) := by
-- proof
  intro i hi
  have hrank : GradedPoset.rank (α := Lmn m n) = m * n := rfl
  rw [hrank] at hi ⊢
  unfold rankCount
  apply Finset.card_nbij complement
  ·
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hp ⊢
    rw [grade_complement, hp]
  ·
    intro p _ q _ h
    exact complement_injective h
  ·
    intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and, Set.mem_image] at hq ⊢
    refine ⟨q.complement, ?_, complement_complement q⟩
    rw [grade_complement]
    have h_le := grade_le_mul q
    omega

end YoungLattice.Lmn

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma ext_eq
  {m n : ℕ}
  {p q : Lmn m n}
-- given
  (h : ∀ i, p.val i = q.val i) :
-- imply
  p = q := by
-- proof
  apply YoungLattice.Lmn.ext h

/--
[zero_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma zero_le_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  zero m n ≤ p := by
-- proof
  apply YoungLattice.Lmn.zero_le p

/--
[sumParts_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma sumParts_zero_eq
  {m n : ℕ} :
-- imply
  sumParts (zero m n) = 0 := by
-- proof
  apply YoungLattice.Lmn.sumParts_zero

/--
[sumParts_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma sumParts_top_eq
  {m n : ℕ} :
-- imply
  sumParts (top m n) = m * n := by
-- proof
  apply YoungLattice.Lmn.sumParts_top

/--
[isMin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma isMin_iff_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  IsMin p ↔ p = zero m n := by
-- proof
  apply YoungLattice.Lmn.isMin_iff

/--
[sumParts_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma sumParts_strictMono_eq
  {m n : ℕ} :
-- imply
  StrictMono (sumParts (m := m) (n := n)) := by
-- proof
  apply YoungLattice.Lmn.sumParts_strictMono

/--
[exists_between](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma exists_between_eq
  {m n : ℕ}
  {p q : Lmn m n}
-- given
  (hle : ∀ i, p.val i ≤ q.val i)
  (hne : p ≠ q)
  (hge2 : sumParts q ≥ sumParts p + 2) :
-- imply
  ∃ r : Lmn m n, p ≤ r ∧ r < q ∧ p ≠ r := by
-- proof
  apply YoungLattice.Lmn.exists_between hle hne hge2

/--
[covBy_sumParts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma covBy_sumParts_eq
  {m n : ℕ}
  {p q : Lmn m n}
-- given
  (h : p ⋖ q) :
-- imply
  sumParts p ⋖ sumParts q := by
-- proof
  apply YoungLattice.Lmn.covBy_sumParts h

/--
[isMin_sumParts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma isMin_sumParts_eq
  {m n : ℕ}
  {p : Lmn m n}
-- given
  (h : IsMin p) :
-- imply
  IsMin (sumParts p) := by
-- proof
  apply YoungLattice.Lmn.isMin_sumParts h

/--
[grade_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma grade_eq_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  grade ℕ p = sumParts p := by
-- proof
  apply YoungLattice.Lmn.grade_eq p

/--
[sumParts_complement_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma sumParts_complement_add_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  sumParts p.complement + sumParts p = m * n := by
-- proof
  apply YoungLattice.Lmn.sumParts_complement_add p

/--
[grade_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLattice.lean)
-/
@[path]
private lemma grade_le_mul_eq
  {m n : ℕ}
  {p : Lmn m n} :
-- imply
  grade ℕ p ≤ m * n := by
-- proof
  apply YoungLattice.Lmn.grade_le_mul p


-- created on 2026-10-23
