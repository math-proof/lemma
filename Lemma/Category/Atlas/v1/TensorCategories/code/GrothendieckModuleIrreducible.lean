import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckModuleIrreducible
open ZPlusModuleIrr


namespace ZPlusModuleIrr

/--
[Lemma_2_8_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckModuleIrreducible.lean)
-/
@[path]
lemma Lemma_2_8_5
  [DecidableEq ι]
  [Fintype ι]
  {R : ZPlusRingIrr ι}
  [DecidableEq κ]
  [Fintype κ]
  {M : ZPlusModuleIrr R κ}
-- given
  (hindec : M.IsIndecomposable)
  (hexact : M.IsExact) :
-- imply
  M.IsIrreducible := by
-- proof
  intro S hS
  have hSc_ne : (Finset.univ \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hS.proper
    have : S = Finset.univ \ (Finset.univ \ S) := by simp
    rw [this, h]; simp
  have hdisj : Disjoint S (Finset.univ \ S) := disjoint_sdiff_self_right
  have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ S)
  have hSc_closed : ∀ (i : ι) (l : κ), l ∈ Finset.univ \ S → ∀ (k : κ),
    M.act i l k ≠ 0 → k ∈ Finset.univ \ S := by
    intro i l hl k hact
    rw [Finset.mem_sdiff] at hl ⊢
    exact ⟨Finset.mem_univ k, fun hk_in_S => by
      obtain ⟨j, hj⟩ := hexact i l k hact
      exact hl.2 (hS.closed j k hk_in_S l hj)⟩
  exact hindec S (Finset.univ \ S) hS.nonempty hSc_ne hdisj hunion hS.closed hSc_closed

end ZPlusModuleIrr


-- created on 2026-10-23
