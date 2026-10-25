/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Def.MathlibExtTest.Topology.InverseLimit
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

example : constTrue ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

example : (fun _ : Fin 2 => false) ∈ InverseLimit.carrier boolId := by
  intro i j _
  rfl

end InverseLimitTest
