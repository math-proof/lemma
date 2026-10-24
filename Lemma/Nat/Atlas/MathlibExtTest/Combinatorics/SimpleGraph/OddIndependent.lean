import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SimpleGraph.OddIndependent


namespace PathGraph3OddTest

/--
[endpoints_indep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma endpoints_indep :
  (SimpleGraph.pathGraph 3).IsIndepSet ({0, 2} : Set (Fin 3)) := by
  classical
  intro u hu w hw hne hadj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
  obtain rfl | rfl <;> rcases hw with rfl | rfl := hu
  · exact absurd rfl hne
  · have h02 : ¬ (SimpleGraph.pathGraph 3).Adj 0 2 := by rw [SimpleGraph.pathGraph_adj]; omega
    exact absurd hadj h02
  · have h20 : ¬ (SimpleGraph.pathGraph 3).Adj 2 0 := by rw [SimpleGraph.pathGraph_adj]; omega
    exact absurd hadj h20
  · exact absurd rfl hne

end PathGraph3OddTest

namespace PathGraph3OddTest

/--
[endpoints_not_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma endpoints_not_odd :
  ¬ (SimpleGraph.pathGraph 3).IsOddIndependent ({0, 2} : Set (Fin 3)) := by
  classical
  intro h
  have h1not : (1 : Fin 3) ∉ ({0, 2} : Set (Fin 3)) := by decide
  obtain ⟨_, h2⟩ := h
  obtain ⟨_, heither⟩ := h2 1 h1not
  have h10 : (SimpleGraph.pathGraph 3).Adj 1 0 := by rw [SimpleGraph.pathGraph_adj]; omega
  have h12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by rw [SimpleGraph.pathGraph_adj]; omega
  have hsub : ({0, 2} : Set (Fin 3)) ⊆
    (SimpleGraph.pathGraph 3).neighborSet 1 := by
    rw [Set.insert_subset_iff]
    constructor
    · rw [SimpleGraph.mem_neighborSet]
      exact h10
    · rw [Set.singleton_subset_iff]
      rwa [SimpleGraph.mem_neighborSet]
  have hinter : (SimpleGraph.pathGraph 3).neighborSet 1 ∩
    ({0, 2} : Set (Fin 3)) = {0, 2} :=
    Set.inter_eq_self_of_subset_right hsub
  rw [hinter] at heither
  obtain hempty | hodd := heither
  · have hmem : (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := by decide
    rw [hempty] at hmem
    exact Set.notMem_empty 0 hmem
  · have hne : (0 : Fin 3) ≠ 2 := by decide
    have hcard : (({0, 2} : Set (Fin 3))).ncard = 2 := Set.ncard_pair hne
    rw [hcard] at hodd
    exact absurd hodd (by decide)

end PathGraph3OddTest


-- created on 2026-10-23
