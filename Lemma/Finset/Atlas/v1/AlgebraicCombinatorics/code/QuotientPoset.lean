import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part2
open Finset MulAction SpernerProperty
open scoped Pointwise


namespace SpernerProperty

/--
[quotientPoset_ne_of_card_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPoset_ne_of_card_ne
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {S T : Finset (Fin n)}
-- given
  (hcard : S.card ≠ T.card) :
-- imply
  (Quotient.mk (orbitRel G _) S) ≠ (Quotient.mk (orbitRel G _) T) := by
-- proof
  intro heq
  exact hcard (card_eq_of_mk_eq heq)

end SpernerProperty

namespace SpernerProperty

/--
[quotientPosetCompl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPosetCompl_mk
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  quotientPosetCompl (Quotient.mk (orbitRel G _) S) = Quotient.mk (orbitRel G _) (Finset.univ \ S) :=
-- proof
  rfl

end SpernerProperty

namespace SpernerProperty

/--
[quotientPosetCompl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPosetCompl_involutive
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  Function.Involutive (quotientPosetCompl (n := n) (G := G)) := by
-- proof
  intro q
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetCompl_mk, sdiff_sdiff_right_self, inf_eq_inter,
      Finset.univ_inter]

end SpernerProperty

namespace SpernerProperty

/--
[quotientPosetCompl_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPosetCompl_bijective
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  Function.Bijective (quotientPosetCompl (n := n) (G := G)) :=
-- proof
  quotientPosetCompl_involutive.bijective

end SpernerProperty

namespace SpernerProperty

/--
[quotientPosetRank_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPosetRank_compl
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {q : QuotientPoset n G} :
-- imply
  quotientPosetRank n G (quotientPosetCompl q) = n - quotientPosetRank n G q := by
-- proof
  induction q using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetCompl_mk, quotientPosetRank_mk]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

end SpernerProperty

namespace SpernerProperty

/--
[quotientPoset_rankCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPoset_rankCount_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {i : ℕ}
-- given
  (hi : i ≤ n) :
-- imply
  (Finset.univ.filter (fun q : QuotientPoset n G => quotientPosetRank n G q = i)).card = (Finset.univ.filter (fun q : QuotientPoset n G => quotientPosetRank n G q = (n - i))).card := by
-- proof
  classical
  apply Finset.card_nbij' quotientPosetCompl quotientPosetCompl
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [quotientPosetRank_compl, hq]
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [quotientPosetRank_compl, hq]
    omega
  · intro q _
    exact quotientPosetCompl_involutive q
  · intro q _
    exact quotientPosetCompl_involutive q

end SpernerProperty

namespace SpernerProperty

/--
[quotientPoset_isRankSymmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
lemma quotientPoset_isRankSymmetric
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  letI := quotientPoset_gradeMinOrder n G letI := quotientPoset_gradedPoset n G IsRankSymmetric (α := QuotientPoset n G) := by
-- proof
  classical
  letI := quotientPoset_gradeMinOrder n G
  letI := quotientPoset_gradedPoset n G
  intro i hi
  unfold rankCount
  simp only [GradedPoset.rank]
  exact quotientPoset_rankCount_eq i hi

end SpernerProperty

/--
[card_eq_of_orbitRel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma card_eq_of_orbitRel_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {S T : Finset (Fin n)}
-- given
  (h : (orbitRel G (Finset (Fin n))).r S T) :
-- imply
  S.card = T.card := by
-- proof
  apply SpernerProperty.card_eq_of_orbitRel h

/--
[card_eq_of_mk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma card_eq_of_mk_eq_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {S T : Finset (Fin n)}
-- given
  (h : (Quotient.mk (orbitRel G (Finset (Fin n))) S) = (Quotient.mk (orbitRel G (Finset (Fin n))) T)) :
-- imply
  S.card = T.card := by
-- proof
  apply SpernerProperty.card_eq_of_mk_eq h

/--
[quotientPosetRank_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_mk_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  quotientPosetRank n G (Quotient.mk _ S) = S.card := by
-- proof
  apply SpernerProperty.quotientPosetRank_mk S

/--
[quotientPosetRank_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_le_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {q : QuotientPoset n G} :
-- imply
  quotientPosetRank n G q ≤ n := by
-- proof
  apply SpernerProperty.quotientPosetRank_le q

/--
[quotientPosetRank_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_univ_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  quotientPosetRank n G (Quotient.mk _ Finset.univ) = n := by
-- proof
  apply SpernerProperty.quotientPosetRank_univ

/--
[mk_smul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma mk_smul_eq_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {g : G}
  {S : Finset (Fin n)} :
-- imply
  Quotient.mk (orbitRel G (Finset (Fin n))) (g • S) = Quotient.mk (orbitRel G (Finset (Fin n))) S := by
-- proof
  apply SpernerProperty.mk_smul_eq g S

/--
[quotientPosetRank_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_strictMono_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))} :
-- imply
  StrictMono (quotientPosetRank n G) := by
-- proof
  apply SpernerProperty.quotientPosetRank_strictMono n G

/--
[quotientPosetRank_covBy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_covBy_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {a b : QuotientPoset n G}
-- given
  (hcov : a ⋖ b) :
-- imply
  quotientPosetRank n G a ⋖ quotientPosetRank n G b := by
-- proof
  apply SpernerProperty.quotientPosetRank_covBy n G hcov

/--
[quotientPosetRank_isMin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma quotientPosetRank_isMin_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {a : QuotientPoset n G}
-- given
  (hmin : IsMin a) :
-- imply
  IsMin (quotientPosetRank n G a) := by
-- proof
  apply SpernerProperty.quotientPosetRank_isMin n G hmin

/--
[smul_compl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean)
-/
@[path]
private lemma smul_compl_eq_eq
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {n : ℕ}
  {G : Subgroup (Equiv.Perm (Fin n))}
  {g : G}
  {S : Finset (Fin n)} :
-- imply
  g • (Finset.univ \ S) = Finset.univ \ (g • S) := by
-- proof
  apply SpernerProperty.smul_compl_eq g S


-- created on 2026-10-23
