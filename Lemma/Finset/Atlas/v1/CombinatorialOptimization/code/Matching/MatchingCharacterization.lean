import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.MatchingCharacterization
open MatchingPolytope
open SimpleGraph Finset


namespace MatchingPolytope

/--
[indicator_is_matching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/MatchingCharacterization.lean)
-/
@[path]
lemma indicator_is_matching
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : Sym2 V → ℕ}
-- given
  (_hx01 : ∀ e ∈ G.edgeFinset, x e = 0 ∨ x e = 1)
  (hdeg : ∀ v : V, ∑ e ∈ G.incidenceFinset v, x e ≤ 1) :
-- imply
  IsMatchingSet G {e | e ∈ G.edgeFinset ∧ x e = 1} := by
-- proof
  refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ v hv₁ hv₂ => ?_⟩
  ·
    simp only [Set.mem_setOf_eq] at he
    exact mem_edgeFinset.mp he.1
  ·
    simp only [Set.mem_setOf_eq] at he₁ he₂
    obtain ⟨he₁_mem, hxe₁⟩ := he₁
    obtain ⟨he₂_mem, hxe₂⟩ := he₂
    by_contra h
    have hv_inc₁ : e₁ ∈ G.incidenceFinset v := by
      rw [mem_incidenceFinset]
      exact ⟨mem_edgeFinset.mp he₁_mem, hv₁⟩
    have hv_inc₂ : e₂ ∈ G.incidenceFinset v := by
      rw [mem_incidenceFinset]
      exact ⟨mem_edgeFinset.mp he₂_mem, hv₂⟩
    have hle : 2 ≤ ∑ e ∈ G.incidenceFinset v, x e := by
      calc 2 = x e₁ + x e₂ := by omega
        _ = ∑ e ∈ ({e₁, e₂} : Finset _), x e := by
          rw [Finset.sum_pair h]
        _ ≤ ∑ e ∈ G.incidenceFinset v, x e :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun e he => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at he
              cases he with
              | inl h => subst h; exact hv_inc₁
              | inr h => subst h; exact hv_inc₂)
            (fun _ _ _ => Nat.zero_le _)
    linarith [hdeg v]

end MatchingPolytope


-- created on 2026-10-23
