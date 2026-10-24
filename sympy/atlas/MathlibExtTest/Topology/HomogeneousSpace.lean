/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/HomogeneousSpace.lean -/


import sympy.atlas.Topology.HomogeneousSpace

example {X : Type*} [TopologicalSpace X] [HomogeneousSpace X] (x y : X) :
    ∃ f : Homeomorph X X, f x = y :=
  HomogeneousSpace.is_transitive x y

/-- Every subsingleton topological space is homogeneous. -/
example (X : Type*) [TopologicalSpace X] [Subsingleton X] : HomogeneousSpace X where
  is_transitive x y := ⟨Homeomorph.refl X, Subsingleton.elim x y⟩

#print axioms HomogeneousSpace
