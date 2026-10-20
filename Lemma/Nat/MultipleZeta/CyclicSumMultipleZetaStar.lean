import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.CyclicSumMultipleZetaStar
open scoped ENNReal
open Topology
open scoped BigOperators
open MetaMathlibExt


/--
[cyclic_sum_formula_multiple_zeta_star_values](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumMultipleZetaStar.lean)
-/
@[path]
private lemma cyclic_sum_formula_multiple_zeta_star_values_eq
  {l : ℕ}
  {k : Fin l → ℕ}
  {cyclicIndex : Fin l → ℕ → MultipleZeta.Index}
  {totalIndex : MultipleZeta.Index}
-- given
  (hl : 0 < l)
  (hk : ∀ j, 0 < k j)
  (hne : ∃ j, k j ≠ 1)
  (hcyclicEntries : ∀ j i, i ∈ Finset.Icc 1 (k j - 1) → (cyclicIndex j i).entries = List.ofFn (fun t : Fin (l + 1) => if t.val = 0 then k j - i + 1 else if t.val = l then i else k ⟨(j.val + t.val) % l, Nat.mod_lt _ hl⟩))
  (hcyclicAdmissible : ∀ j i, (cyclicIndex j i).IsAdmissibleOrEmpty)
  (htotalEntries : totalIndex.entries = [(∑ j : Fin l, k j) + 1])
  (htotalAdmissible : totalIndex.IsAdmissibleOrEmpty) :
-- imply
  ∑ j : Fin l, ∑ i ∈ Finset.Icc 1 (k j - 1),
    MultipleZeta.starValue (cyclicIndex j i) (hcyclicAdmissible j i) =
    ((∑ j : Fin l, k j : ℕ) : ℝ) *
    MultipleZeta.strictValue totalIndex htotalAdmissible := by
-- proof
  apply MetaMathlibExt.cyclic_sum_formula_multiple_zeta_star_values l hl k hk hne cyclicIndex hcyclicEntries hcyclicAdmissible totalIndex htotalEntries htotalAdmissible


-- created on 2026-10-20
