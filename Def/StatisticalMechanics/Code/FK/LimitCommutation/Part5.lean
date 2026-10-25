/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


def lmc_freePlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ Tendsto
            (fun m : ℕ => lmc_transBoxMassFree (Multiplicative.toAdd g⁻¹) N t p (N + m)
              (Nat.le_add_right N m)) atTop
            (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))))


end FK
end StatMech
