/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/IndependentSet.lean -/


import Def.Combinatorics.SetFamily.IndependentSet
import Lemma.Finset.SetFamily.IndependentSet
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
open SetFamily

/-!
# Examples for hypergraph independent sets and Steiner triple systems

Positive and negative examples for `SetFamily.IsIndependent` and
`SetFamily.IsSteinerTripleSystem`, plus the persistence and projection API.
-/


/-- Positive example: neither edge is contained in `{0, 2}`. -/
example : IsIndependent
    (({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
      Finset (Finset (Fin 3)))) ({0, 2} : Finset (Fin 3)) := by
  unfold IsIndependent
  decide

/-- Negative example: the edge `{0, 1}` is contained in `{0, 1, 2}`. -/
example : ¬ IsIndependent
    (({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))))
    ({0, 1, 2} : Finset (Fin 3)) := by
  unfold IsIndependent
  decide

/-- The empty vertex set is independent when the edge is nonempty. -/
example : IsIndependent
    (({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3)))) ∅ := by
  rw [isIndependent_empty_iff]
  decide

/-- Independence persists to subsets. -/
example (h : IsIndependent
    (({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))))
    ({0, 2} : Finset (Fin 3))) :
    IsIndependent (({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))))
      ({0} : Finset (Fin 3)) :=
  isIndependent_of_subset h (by decide)

/-- Positive example: the single triple on three vertices is a Steiner triple
system. -/
example : IsSteinerTripleSystem
    (({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))) := by
  refine ⟨by unfold SetFamily.IsUniform; decide, ?_⟩
  intro u v huv
  fin_cases u <;> fin_cases v
  · simp_all
  · exact existsUnique_mem_singleton (by decide)
  · exact existsUnique_mem_singleton (by decide)
  · exact existsUnique_mem_singleton (by decide)
  · simp_all
  · exact existsUnique_mem_singleton (by decide)
  · exact existsUnique_mem_singleton (by decide)
  · exact existsUnique_mem_singleton (by decide)
  · simp_all

/-- Negative example: a 2-edge violates 3-uniformity. -/
example : ¬ IsSteinerTripleSystem
    (({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3)))) := by
  intro h
  have hcard := h.1 _ (Finset.mem_singleton_self _)
  have h2 : (({0, 1} : Finset (Fin 3)).card) = 2 := by decide
  omega

/-- Negative example: the pair `(0, 1)` lies in two edges. -/
example : ¬ IsSteinerTripleSystem
    (({({0, 1, 2} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4))} :
      Finset (Finset (Fin 4)))) := by
  intro h
  have h01 := h.2 0 1 (by decide)
  have e1 : ({0, 1, 2} : Finset (Fin 4)) ∈
      (({({0, 1, 2} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4))} :
        Finset (Finset (Fin 4)))) ∧
      (0 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) ∧
      (1 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have e2 : ({0, 1, 3} : Finset (Fin 4)) ∈
      (({({0, 1, 2} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4))} :
        Finset (Finset (Fin 4)))) ∧
      (0 : Fin 4) ∈ ({0, 1, 3} : Finset (Fin 4)) ∧
      (1 : Fin 4) ∈ ({0, 1, 3} : Finset (Fin 4)) := by decide
  have heq := h01.unique e1 e2
  revert heq
  decide

/-- Uniformity projection on the single-triple system. -/
example (h : IsSteinerTripleSystem
    (({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))))) :
    IsUniform (({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))) 3 :=
  uniform_of_isSteinerTripleSystem h

