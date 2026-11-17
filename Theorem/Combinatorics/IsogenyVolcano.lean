/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Def.Combinatorics.IsogenyVolcano
set_option autoImplicit false

open BigOperators

/-!
# Isogeny volcanoes on multigraphs

This file defines symmetric multigraphs by edge multiplicity and the combinatorial structure of
an isogeny volcano. Loops are permitted. The degree counts a loop's multiplicity once, following
the outgoing-isogeny convention rather than the convention where an undirected loop counts twice.
-/

public section


namespace Multigraph

variable {V : Type*}

/-- Every vertex connects to itself. -/
theorem connected_refl (G : Multigraph V) (v : V) :
    G.Connected v v :=
  Relation.ReflTransGen.refl

end Multigraph
