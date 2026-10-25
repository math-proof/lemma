/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Def.MathlibExtTest.Topology.InverseLimit.Part4
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

example (a : Fin 3) : (fun _ : Fin 2 => a) ∈ InverseLimit.carrier finId := by
  intro i j _
  rfl

example : IsCompact (InverseLimit.carrier finId) := by
  apply InverseLimit.isCompact_carrier (f := finId)
  intro i j _
  exact continuous_id

end InverseLimitTest
