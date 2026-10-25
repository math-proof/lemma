/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

section Partition

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  (P : U → Prop) [DecidablePred P]


theorem agl_fkZ_eq (p q : ℝ) :
    fkZ K₀ p q = fkZ (agl_glueGraph K₀ P) p q :=
  fsm_fkZ_iso K₀ (agl_glueGraph K₀ P) (agl_iso K₀ P) p q


theorem agl_neglog_partition_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    -Real.log (fkZ K₀ p q)
      ≤ -Real.log (fkZ (agl_left K₀ P) p q) + -Real.log (fkZ (agl_right K₀ P) p q)
        - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
  rw [agl_fkZ_eq K₀ P p q]
  exact fis_neglog_interface_le (agl_partitionCrossInterface K₀ P) hp hp1 hq

end Partition


open StatMech.Lattice


theorem agl_nn_translate (d : ℕ) (v x y : Site d) :
    (hypercubicLattice d).Adj (x + v) (y + v) ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [← h] <;>
    refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]

end FK
end StatMech
