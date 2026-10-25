/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
import Theorem.MathlibExtTest.Topology.InverseLimit
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

/-- A non-constant tuple over `Fin 2` violates compatibility at `0 ≤ 1`. -/
def mixed : Fin 2 → Bool := ![true, false]

end InverseLimitTest
