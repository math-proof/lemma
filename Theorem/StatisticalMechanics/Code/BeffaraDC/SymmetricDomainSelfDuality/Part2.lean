/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Instance.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part6
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem mixedConnected_iff_openConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.MixedConnected omega ↔ D.OpenConnected omega := by
  let O := FK.openSub D.finiteGraph omega
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    apply hxy.elim
    intro p
    let P : D.Vertex → Prop := fun z =>
      (∃ a, D.OnGammaOne a ∧ O.Reachable a z) ∨ D.OpenConnected omega
    have hP : P y :=
      (SimpleGraph.Walk.concatRec
        (motive := fun u z _ => D.OnGammaOne u → P z)
        (fun {u} hu => Or.inl ⟨u, hu, SimpleGraph.Reachable.rfl⟩)
        (fun {u v w} p huv ih hu => by
          have ih' := ih hu
          rw [SimpleGraph.sup_adj, mixedWiring, SimpleGraph.sup_adj] at huv
          rcases huv with hopen | hone | htwo
          · rcases ih' with ⟨a, ha, hau⟩ | hconn
            · exact Or.inl ⟨a, ha, hau.trans hopen.reachable⟩
            · exact Or.inr hconn
          · rcases ih' with hreach | hconn
            · have hw : D.OnGammaOne w :=
                (StatMech.Lattice.boundaryCliqueGraph_adj
                  D.OnGammaOne v w).mp hone |>.2.2
              exact Or.inl ⟨w, hw, SimpleGraph.Reachable.rfl⟩
            · exact Or.inr hconn
          · rcases ih' with ⟨a, ha, hau⟩ | hconn
            · have hv : D.OnGammaTwo v :=
                (StatMech.Lattice.boundaryCliqueGraph_adj
                  D.OnGammaTwo v w).mp htwo |>.2.1
              exact Or.inr ⟨a, v, ha, hv, hau⟩
            · exact Or.inr hconn)
        p) hx
    rcases hP with ⟨a, ha, hay⟩ | hconn
    · exact ⟨a, y, ha, hy, hay⟩
    · exact hconn
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, hxy.mono le_sup_left⟩


end SymmetricDomain
end
end BeffaraDC
end StatMech
