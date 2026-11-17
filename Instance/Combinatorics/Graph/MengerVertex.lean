/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Lattice.Nat
public import Def.Combinatorics.Graph.MengerVertex

@[expose] public section

section

namespace MetaMathlibExt

noncomputable instance decIsListStep {W : Type*} (l : List W) (a b : W) :
    Decidable (isListStep l a b) :=
  Classical.propDecidable _

end MetaMathlibExt
end
