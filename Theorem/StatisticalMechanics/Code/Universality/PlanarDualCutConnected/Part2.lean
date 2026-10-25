/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
import Def.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem pdc_rot90Hom_apply (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (a : Site 2) :
    pdc_rot90Hom ω n a = rot90Fun a := rfl


theorem pdc_rot90Inv_adj_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    (pdc_barrierGraphPrimal ω n).Adj (rot90Inv p) (rot90Inv q) := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hinvrot : ∀ x : Site 2, rot90Inv (rot90Fun x) = x := fun x => rot90Equiv.left_inv x
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · refine ⟨v, w, hvw, Or.inl ⟨?_, ?_⟩⟩
    · rw [hp, hinvrot]
    · rw [hq, hinvrot]
  · refine ⟨v, w, hvw, Or.inr ⟨?_, ?_⟩⟩
    · rw [hp, hinvrot]
    · rw [hq, hinvrot]


end Universality
end StatMech
