import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle.Part2
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle


namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle

/--
[complete_three_hasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/StrongSquareCycle.lean)
-/
@[path]
lemma complete_three_hasStrongSquareCycle
-- imply
  (⊤ : SimpleGraph (Fin 3)).HasStrongSquareCycle 0 := by
-- proof
  have hcycle : triangleWalk.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    simp [SimpleGraph.Walk.isPath_def, triangleWalk]
  have hhamiltonian : triangleWalk.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hcycle, by simp [triangleWalk]⟩
  refine ⟨triangleWalk, hhamiltonian, ?_, ?_⟩ <;> simp [triangleWalk]

end MathlibExtTest.Combinatorics.SimpleGraph.StrongSquareCycle


-- created on 2026-10-23
