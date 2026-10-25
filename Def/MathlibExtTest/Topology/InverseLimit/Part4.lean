/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Theorem.MathlibExtTest.Topology.InverseLimit.Part3
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

/-- Constant `Fin 3` family with identity maps: diagonal tuples are limits. -/
def finId : ∀ ⦃i j : Fin 2⦄, i ≤ j → Fin 3 → Fin 3 := fun {_ _} _ => id

end InverseLimitTest
