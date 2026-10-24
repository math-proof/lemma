/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Saturation.lean -/

-- MathlibExt/Combinatorics/SimpleGraph/Saturation.lean

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Minimal

/-!
# Graph saturation and the saturation number

Source: Huanying Bian, Qing Cui, Shengjin Ji, and Fuhong Ma,
*On the saturation number of the kite graph*, arXiv:2608.16069v1.

For a fixed graph `H`, a graph `G` is `H`-saturated if `G` does not contain a
copy of `H`, but for any edge `e` not in `E(G)`, the graph `G + e` contains a
copy of `H`. The saturation number `sat(n, H)` is the minimum size of an
`H`-saturated graph on `n` vertices.

Representation: `H`-saturation is maximal `H`-freeness (`Maximal H.Free G`) in
the graph-inclusion order, with the equivalence to the source's missing-edge
formulation proved below. `sat` is the infimum of edge counts over saturated
graphs on `Fin n`; it equals `0` when no saturated graph exists.
-/

namespace SimpleGraph

variable {V W : Type*} (H : SimpleGraph V)

/-- `H`-saturation: `G` is `H`-free and maximal with that property in the
graph-inclusion order. -/
def IsSaturated (G : SimpleGraph W) : Prop :=
  Maximal H.Free G

/-- Edge counts of `H`-saturated graphs on `Fin n`. -/
def satCounts (n : ℕ) : Set ℕ :=
  { m | ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj, H.IsSaturated G ∧
    G.edgeFinset.card = m }

/-- The saturation number `sat(n, H)`: the minimum size of an `H`-saturated
graph on `n` vertices. This is `0` when no saturated graph exists. -/
noncomputable def sat (n : ℕ) : ℕ :=
  sInf (H.satCounts n)
end SimpleGraph
