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
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part17
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem unionConnected_all (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.UnionConnected omega := by
  let x := D.gammaOneStart
  let y := D.gammaTwoStart
  refine ⟨x, y, onGammaOne_gammaOneStart D,
    onGammaTwo_gammaTwoStart D, ?_⟩
  by_cases hxy : x = y
  · rw [hxy]
  · apply Adj.reachable
    rw [SimpleGraph.sup_adj]
    exact Or.inr ((StatMech.Lattice.boundaryCliqueGraph_adj
      (fun z : D.Vertex => D.OnGammaOne z ∨ D.OnGammaTwo z) x y).2
        ⟨hxy, Or.inl (onGammaOne_gammaOneStart D),
          Or.inr (onGammaTwo_gammaTwoStart D)⟩)


theorem no_unionWiring_dual_complement (D : SymmetricDomain) :
    ¬∃ dual : ConfigSpace (Sym2 D.Vertex) ≃ ConfigSpace (Sym2 D.Vertex),
      ∀ omega, D.UnionConnected (dual omega) ↔ ¬D.UnionConnected omega := by
  rintro ⟨dual, hdual⟩
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hleft : D.UnionConnected (dual omega) := unionConnected_all D _
  have hright : ¬D.UnionConnected omega := (hdual omega).mp hleft
  exact hright (unionConnected_all D omega)

end SymmetricDomain
end
end BeffaraDC
end StatMech
