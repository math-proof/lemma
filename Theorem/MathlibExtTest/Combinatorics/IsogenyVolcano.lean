module
public import Instance.Combinatorics.IsogenyVolcano.Part2
public import Theorem.Finset.IsogenyVolcano
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Combinatorics.IsogenyVolcano
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/

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

