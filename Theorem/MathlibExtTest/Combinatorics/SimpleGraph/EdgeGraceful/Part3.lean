/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Def.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful
import Def.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful.Part2


namespace EdgeGracefulTest

theorem hto01 : pathToFun e01 = 0 := by simp [pathToFun, he01]

theorem hto12 : pathToFun e12 = 1 := by simp [pathToFun, he12]

theorem hinv0 : pathInvFun 0 = e01 := by simp [pathInvFun]

theorem hinv1 : pathInvFun 1 = e12 := by simp [pathInvFun]

theorem sclass : ∀ s : Sym2 (Fin 3),
    s ∈ (SimpleGraph.pathGraph 3).edgeSet →
      s = Sym2.mk (0 : Fin 3) 1 ∨ s = Sym2.mk (1 : Fin 3) 2 :=
  fun s hs => Sym2.ind (fun a b h => by
    have hadj : (SimpleGraph.pathGraph 3).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp h
    fin_cases a <;> fin_cases b
    · simp at hadj
    · exact Or.inl rfl
    · simp [SimpleGraph.pathGraph_adj] at hadj
    · exact Or.inl (by decide)
    · simp at hadj
    · exact Or.inr rfl
    · simp [SimpleGraph.pathGraph_adj] at hadj
    · exact Or.inr (by decide)
    · simp at hadj) s hs

theorem eclass : ∀ e : (SimpleGraph.pathGraph 3).edgeSet, e = e01 ∨ e = e12 := by
  intro e
  have h := sclass _ e.property
  rcases h with h | h
  · left
    apply Subtype.ext
    rw [h, he01]
  · right
    apply Subtype.ext
    rw [h, he12]

end EdgeGracefulTest
