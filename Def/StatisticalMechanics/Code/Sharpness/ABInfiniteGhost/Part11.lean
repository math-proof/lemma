/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part10
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


def abigDartFiberEquivNeighbor {W : Type*} (H : SimpleGraph W) (x : W) :
    {d : H.Dart // d.fst = x} ≃ H.neighborSet x where
  toFun d := ⟨d.1.snd, by simpa only [d.2] using d.1.adj⟩
  invFun y := ⟨H.dartOfNeighborSet x y, rfl⟩
  left_inv d := by
    rcases d with ⟨⟨⟨a, b⟩, hab⟩, ha⟩
    simp only at ha
    subst a
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl


end Sharpness
end StatMech
