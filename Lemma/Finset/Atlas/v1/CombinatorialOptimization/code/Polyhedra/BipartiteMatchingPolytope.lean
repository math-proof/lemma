import Mathlib
import sympy.Basic
import Def.v1.Atlas.CombinatorialOptimization.code.Polyhedra.BipartiteMatchingPolytope
open SimpleGraph Finset Matrix BipartiteMatchingPolytope


namespace BipartiteMatchingPolytope

/--
[constraintMatrix_TU_of_bipartite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/BipartiteMatchingPolytope.lean)
-/
@[path]
lemma constraintMatrix_TU_of_bipartite
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq (Sym2 V)]
-- given
  (hG : G.IsBipartite) :
-- imply
  ((incMatrix ℤ G).fromRows (-1 : Matrix (Sym2 V) (Sym2 V) ℤ)).IsTotallyUnimodular :=
-- proof
  SimpleGraph.constraintMatrix_isTotallyUnimodular_of_isBipartite G hG

end BipartiteMatchingPolytope

namespace BipartiteMatchingPolytope

/--
[matchingLPRelaxation_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/BipartiteMatchingPolytope.lean)
-/
@[path]
lemma matchingLPRelaxation_convex
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Convex ℝ (matchingLPRelaxation G) := by
-- proof
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro e
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [mul_nonneg ha (hx.1 e), mul_nonneg hb (hy.1 e)]
  · intro v
    calc ∑ e ∈ G.incidenceFinset v, (a • x + b • y) e
      = a * ∑ e ∈ G.incidenceFinset v, x e + b * ∑ e ∈ G.incidenceFinset v, y e := by
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ a * 1 + b * 1 := by gcongr; exact hx.2.1 v; exact hy.2.1 v
      _ = 1 := by linarith
  · intro e he
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.2.2 e he, hy.2.2 e he]

end BipartiteMatchingPolytope

namespace BipartiteMatchingPolytope

/--
[matchingIndicators_subset_matchingLPRelaxation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/BipartiteMatchingPolytope.lean)
-/
@[path]
lemma matchingIndicators_subset_matchingLPRelaxation
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  matchingIndicators G ⊆ matchingLPRelaxation G := by
-- proof
  intro x hx
  obtain ⟨M, hM_sub, hM_match, hx_eq⟩ := hx
  subst hx_eq
  refine ⟨?_, ?_, ?_⟩
  · intro e; simp only; split_ifs <;> linarith
  · intro v; simp only
    have hsum : ∑ e ∈ G.incidenceFinset v, (if e ∈ M then (1 : ℝ) else 0) =
      ((G.incidenceFinset v).filter (· ∈ M)).card := by
      rw [← Finset.sum_filter, Finset.card_eq_sum_ones]; simp
    rw [hsum]
    suffices h : ((G.incidenceFinset v).filter (· ∈ M)).card ≤ 1 by exact_mod_cast h
    by_contra hgt
    push_neg at hgt
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp hgt
    simp only [Finset.mem_filter, mem_incidenceFinset] at he₁ he₂
    exact hne (hM_match e₁ he₁.2 e₂ he₂.2 v he₁.1.2 he₂.1.2)
  · intro e he; simp only
    have : e ∉ M := fun hm => he (mem_edgeFinset.mpr (hM_sub hm))
    simp [this]

end BipartiteMatchingPolytope

namespace BipartiteMatchingPolytope

/--
[convexHull_matchingIndicators_subset_matchingLPRelaxation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Polyhedra/BipartiteMatchingPolytope.lean)
-/
@[path]
lemma convexHull_matchingIndicators_subset_matchingLPRelaxation
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  (convexHull ℝ) (matchingIndicators G) ⊆ matchingLPRelaxation G :=
-- proof
  convexHull_min (matchingIndicators_subset_matchingLPRelaxation G)
    (matchingLPRelaxation_convex G)

end BipartiteMatchingPolytope


-- created on 2026-10-23
