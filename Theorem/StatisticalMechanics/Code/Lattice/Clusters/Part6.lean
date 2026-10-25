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
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part6
open Set


namespace StatMech

namespace Lattice

variable {d : ℕ}


theorem connectedWithin_refl (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d))
    (x : S) : ConnectedWithin d ω S x x := SimpleGraph.Reachable.refl x

theorem ConnectedWithin.symm {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y : S} (h : ConnectedWithin d ω S x y) : ConnectedWithin d ω S y x :=
  SimpleGraph.Reachable.symm h

theorem ConnectedWithin.trans {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y z : S} (hxy : ConnectedWithin d ω S x y) (hyz : ConnectedWithin d ω S y z) :
    ConnectedWithin d ω S x z := SimpleGraph.Reachable.trans hxy hyz


theorem ConnectedWithin.connected {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {x y : S} (h : ConnectedWithin d ω S x y) : Connected d ω x y := by
  have hmap : (openSubgraphInduce d ω S).Reachable x y →
      (openSubgraph d ω).Reachable (x : Site d) (y : Site d) :=
    fun hr => hr.map (SimpleGraph.Embedding.induce S).toHom
  exact hmap h


end Lattice
end StatMech
