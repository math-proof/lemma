/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/InverseLimit.lean -/


import Def.Topology.InverseLimit
import Lemma.Set.InverseLimit
/-!
# Inverse-limit smoke tests

Concrete identity systems over `Fin 2` and `Unit` exercising
`InverseLimit.carrier`, compatibility, closedness, and compactness.
-/


namespace InverseLimitTest

/-- Identity transition maps on the constant `Bool` family over `Fin 2`. -/
def boolId : ∀ ⦃i j : Fin 2⦄, i ≤ j → Bool → Bool := fun {_ _} _ => id

/-- The constant `true` tuple is compatible. -/
def constTrue : Fin 2 → Bool := fun _ => true

end InverseLimitTest
