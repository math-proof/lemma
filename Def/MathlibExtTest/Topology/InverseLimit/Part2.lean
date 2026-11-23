/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/

module

public import Def.Topology.InverseLimit
public import Theorem.Set.InverseLimit
public import Theorem.MathlibExtTest.Topology.InverseLimit

@[expose] public section

/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

/-- A non-constant tuple over `Fin 2` violates compatibility at `0 ≤ 1`. -/
def mixed : Fin 2 → Bool := ![true, false]

end InverseLimitTest
