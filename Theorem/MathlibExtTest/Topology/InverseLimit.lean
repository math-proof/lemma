/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/
module

public import Def.Topology.InverseLimit
public import Theorem.Set.InverseLimit
public import Def.MathlibExtTest.Topology.InverseLimit

/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/

public section


namespace InverseLimitTest

example : constTrue ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

example : (fun _ : Fin 2 => false) ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

end InverseLimitTest
