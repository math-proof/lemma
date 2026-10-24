/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StrongSquareCycle.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle


namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

private theorem adj_zero_one :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 0 1 :=
  ⟨by decide, Or.inl (by simp)⟩

private theorem adj_one_two :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 1 2 :=
  ⟨by decide, Or.inl (by simp)⟩

private theorem adj_two_zero :
    (⊤ : SimpleGraph (Fin 3)).square.Adj 2 0 :=
  ⟨by decide, Or.inl (by simp)⟩

private def triangleWalk :
    (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0 :=
  .cons adj_zero_one (.cons adj_one_two (.cons adj_two_zero .nil))

example :
    ∃ p : (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0, p.IsHamiltonianCycle := by
  obtain ⟨p, hp, -, -⟩ :=
    (SimpleGraph.hasStrongSquareCycle_iff (⊤ : SimpleGraph (Fin 3)) 0).mp
      complete_three_hasStrongSquareCycle
  exact ⟨p, hp⟩

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle
