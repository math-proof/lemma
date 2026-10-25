/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Theorem.MathlibExtTest.Topology.InverseLimit.Part2
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

/-- Singleton index: every tuple is compatible with the identity transition map. -/
def unitId : ∀ ⦃i j : Unit⦄, i ≤ j → Bool → Bool := fun {_ _} _ => id

end InverseLimitTest
