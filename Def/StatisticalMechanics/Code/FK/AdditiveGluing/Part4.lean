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
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part3
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

open StatMech.Lattice


variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


noncomputable def agl_leftBlockIso (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) :
    boxGraph d m ≃g agl_left (boxGraph d N) P where
  toEquiv := φ
  map_rel_iff' := by
    intro y z
    
    show (agl_left (boxGraph d N) P).Adj (φ y) (φ z) ↔ (boxGraph d m).Adj y z
    unfold agl_left boxGraph
    simp only [comap_adj]
    rw [hφ y, hφ z]
    exact agl_nn_translate d v (y : Site d) (z : Site d)


end FK
end StatMech
