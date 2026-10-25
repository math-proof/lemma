/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part10
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


noncomputable def ecz_cellEquiv (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    boxVerts d m ≃ {x : boxVerts d n // ecz_vanHoveTag m n x = some c} where
  toFun y := ⟨⟨fun i => (y : Site d) i + ecz_center m n c i,
      ecz_center_mem_box m n c (y : Site d) y.2⟩, by
    rw [ecz_vanHoveTag_eq_some_iff]; intro i; simp only [add_sub_cancel_right]
    exact (qp_natAbs_iff ((y : Site d) i) m).mpr ((qp_natAbs_iff ((y : Site d) i) m).mp (y.2 i))⟩
  invFun x := ⟨fun i => ((x : boxVerts d n) : Site d) i - ecz_center m n c i, by
    have h := (ecz_vanHoveTag_eq_some_iff m n x.1 c).mp x.2
    intro i; exact h i⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; funext i; simp


noncomputable def ecz_cellBlockIso (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    boxGraph d m ≃g qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c) where
  toEquiv := ecz_cellEquiv m n c
  map_rel_iff' := by
    intro y z
    show (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)).Adj
        (ecz_cellEquiv m n c y) (ecz_cellEquiv m n c z) ↔ (boxGraph d m).Adj y z
    unfold qp_blkG boxGraph
    simp only [comap_adj]
    show (hypercubicLattice d).Adj
        (fun i => (y : Site d) i + ecz_center m n c i) (fun i => (z : Site d) i + ecz_center m n c i)
      ↔ (hypercubicLattice d).Adj (y : Site d) (z : Site d)
    exact agl_nn_translate d (ecz_center m n c) (y : Site d) (z : Site d)


end VanHove
end BoxNesting
end FK
end StatMech
