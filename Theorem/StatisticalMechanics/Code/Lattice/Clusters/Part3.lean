/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part3
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


theorem connected_refl (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    Connected d ω x x := SimpleGraph.Reachable.refl x

@[refl]
theorem connected_rfl {ω : ConfigSpace (Sym2 (Site d))} {x : Site d} :
    Connected d ω x x := SimpleGraph.Reachable.refl x

theorem Connected.symm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : Connected d ω x y) : Connected d ω y x := SimpleGraph.Reachable.symm h

theorem Connected.trans {ω : ConfigSpace (Sym2 (Site d))} {x y z : Site d}
    (hxy : Connected d ω x y) (hyz : Connected d ω y z) : Connected d ω x z :=
  SimpleGraph.Reachable.trans hxy hyz

theorem connected_comm {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d} :
    Connected d ω x y ↔ Connected d ω y x := SimpleGraph.reachable_comm


theorem connected_equivalence (ω : ConfigSpace (Sym2 (Site d))) :
    Equivalence (Connected d ω) := (openSubgraph d ω).reachable_is_equivalence


theorem IsOpenEdge.connected {ω : ConfigSpace (Sym2 (Site d))} {x y : Site d}
    (h : IsOpenEdge d ω x y) : Connected d ω x y :=
  SimpleGraph.Adj.reachable (G := openSubgraph d ω) h


end Lattice
end StatMech
