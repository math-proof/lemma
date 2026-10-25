/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/IsogenyVolcano.lean -/


import Instance.Combinatorics.IsogenyVolcano.Part2
import Lemma.Finset.IsogenyVolcano
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Combinatorics.IsogenyVolcano.Part2
set_option autoImplicit false


example : depthOneVolcano.isSurface false := rfl

example : depthOneVolcano.isFloor true := rfl

example : depthOneVolcano.IsDescendingEdge false true := by
  refine ⟨?_, rfl⟩
  decide

example : depthOneVolcano.IsAscendingEdge true false := by
  refine ⟨?_, rfl⟩
  decide

example :
    depthOneVolcano.IsDescendingEdge false true ↔
      depthOneVolcano.IsAscendingEdge true false :=
  IsogenyVolcano.descending_iff_ascending_symm
    (C := depthOneVolcano) false true

example :
    depthOneVolcano.IsHorizontalEdge false true ∨
      depthOneVolcano.IsDescendingEdge false true ∨
        depthOneVolcano.IsAscendingEdge false true := by
  apply IsogenyVolcano.edge_direction (C := depthOneVolcano) false true
  decide

