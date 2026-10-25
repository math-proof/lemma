/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean -/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Def.Combinatorics.Graph.MengerVertex


section

namespace MetaMathlibExt

noncomputable instance decIsListStep {W : Type*} (l : List W) (a b : W) :
    Decidable (isListStep l a b) :=
  Classical.propDecidable _

end MetaMathlibExt
end
