/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.PercoSusceptibility
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def shk_translateInduceIso (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d)) :
    openSubgraphInduce d omega (S : Set (Site d)) ≃g
      openSubgraphInduce d (ConfigSpace.shift g omega)
        (shk_translateFinset g S : Set (Site d)) where
  toEquiv :=
    { toFun := fun x => ⟨g • (x : Site d), by
          exact shk_mem_translateFinset_smul g S x |>.2 x.2⟩
      invFun := fun x => ⟨g⁻¹ • (x : Site d), by
          have hx : g • (g⁻¹ • (x : Site d)) ∈ shk_translateFinset g S := by
            simpa only [smul_inv_smul] using x.2
          exact (shk_mem_translateFinset_smul g S _).1 hx⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp only [inv_smul_smul]
      right_inv := fun x => by
        apply Subtype.ext
        simp only [smul_inv_smul] }
  map_rel_iff' := by
    intro x y
    simp only [openSubgraphInduce_adj]
    exact openSubgraph_adj_shift g omega x y


end Sharpness
end StatMech
