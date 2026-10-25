/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Def.MathlibExtTest.Topology.InverseLimit.Part3
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

example (x : Unit → Bool) : x ∈ InverseLimit.carrier unitId := by
  intro i j _
  cases i
  cases j
  rfl

end InverseLimitTest
