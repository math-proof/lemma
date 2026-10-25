/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangLowerBound
import Structure.StatisticalMechanics.Code.TwoDim.ZhangClose
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


def zhg_geometricData_satisfiable {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] :
    ZhangGeometricData μ (fun _ => (univ : Set (ConfigSpace E))) (fun _ => univ) where
  S := fun _ _ => univ
  Err := fun _ => ∅
  Sinc := fun _ _ => isUpperSet_univ
  Sm := fun _ _ => MeasurableSet.univ
  Ssym := fun _ _ => rfl
  errTendsto := by simp [measureReal_empty]
  unionTendsto := by simp only [Set.union_self, probReal_univ]; exact tendsto_const_nhds
  merge := fun _ => by simp


end TwoDim
end StatMech
