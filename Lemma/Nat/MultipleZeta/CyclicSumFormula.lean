import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.CyclicSumFormula
open scoped ENNReal
open Topology
open scoped BigOperators
open MetaMathlibExt
open CyclicSumFormula


/--
[leftIndex_isAdmissibleOrEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumFormula.lean)
-/
@[path]
private lemma leftIndex_isAdmissibleOrEmpty_eq
  {k : List ℕ}
  {j : Fin k.length}
  {i : ℕ}
-- given
  (hk_pos : ∀ n ∈ k, 1 ≤ n) :
-- imply
  (leftIndex k hk_pos j i).IsAdmissibleOrEmpty := by
-- proof
  apply MetaMathlibExt.CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i

/--
[rightIndex_isAdmissibleOrEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumFormula.lean)
-/
@[path]
private lemma rightIndex_isAdmissibleOrEmpty_eq
  {k : List ℕ}
  {j : Fin k.length}
-- given
  (hk_pos : ∀ n ∈ k, 1 ≤ n) :
-- imply
  (rightIndex k hk_pos j).IsAdmissibleOrEmpty := by
-- proof
  apply MetaMathlibExt.CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j

/--
[hoffman_ohno_cyclic_sum_formula_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumFormula.lean)
-/
@[path]
private lemma hoffman_ohno_cyclic_sum_formula_strict_eq
  {k : List ℕ}
-- given
  (hk_nonempty : k ≠ [])
  (hk_pos : ∀ n ∈ k, 1 ≤ n)
  (hk_not_all_one : ∃ n ∈ k, n ≠ 1) :
-- imply
  ∑ j : Fin k.length,
    ∑ i ∈ Finset.Icc 1 (k.get j - 1),
    MultipleZeta.strictValue (leftIndex k hk_pos j i)
    (leftIndex_isAdmissibleOrEmpty k hk_pos j i) =
    ∑ j : Fin k.length,
    MultipleZeta.strictValue (rightIndex k hk_pos j)
    (rightIndex_isAdmissibleOrEmpty k hk_pos j) := by
-- proof
  apply MetaMathlibExt.hoffman_ohno_cyclic_sum_formula_strict k hk_nonempty hk_pos hk_not_all_one

/--
[hoffman_ohno_cyclic_sum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumFormula.lean)
-/
@[path]
private lemma hoffman_ohno_cyclic_sum_formula_eq
  {k : List ℕ}
-- given
  (hk_nonempty : k ≠ [])
  (hk_pos : ∀ n ∈ k, 1 ≤ n)
  (hk_not_all_one : ∃ n ∈ k, n ≠ 1) :
-- imply
  ∑ j : Fin k.length,
    ∑ i ∈ Finset.Icc 1 (k.get j - 1),
    multipleZetaValue
    ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) =
    ∑ j : Fin k.length,
    multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) := by
-- proof
  apply MetaMathlibExt.hoffman_ohno_cyclic_sum_formula k hk_nonempty hk_pos hk_not_all_one


-- created on 2026-10-20
