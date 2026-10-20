/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/HomogeneousSpace.lean -/

/-
# Homogeneous topological spaces
-/

import Mathlib.Topology.Homeomorph.Defs

/-- A topological space is homogeneous if its homeomorphism group acts transitively. -/
class HomogeneousSpace (X : Type*) [TopologicalSpace X] : Prop where
  is_transitive : ∀ x y : X, ∃ f : Homeomorph X X, f x = y
