/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/


import Instance.Combinatorics.IsogenyVolcano.Part2
import Lemma.Finset.IsogenyVolcano
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Combinatorics.IsogenyVolcano
set_option autoImplicit false


example : singletonLoopVolcano.isSurface () := rfl

example : singletonLoopVolcano.isFloor () := rfl

example : singletonLoopVolcano.graph.degree () = 2 := by
  change Finset.sum Finset.univ (fun _ : Unit => 2) = 2
  simp

example : singletonLoopVolcano.IsHorizontalEdge () () := by
  refine ⟨?_, rfl, rfl⟩
  decide

example :
    singletonLoopVolcano.IsHorizontalEdge () () ∨
      singletonLoopVolcano.IsDescendingEdge () () ∨
        singletonLoopVolcano.IsAscendingEdge () () := by
  apply IsogenyVolcano.edge_direction (C := singletonLoopVolcano) () ()
  decide

