/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose
open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]


variable {d : ℕ}


instance bkc_isProbMeasure_factor (p : ℝ≥0) (hp : p ≤ 1) (e : Sym2 (Site d))
    (F : Finset (Sym2 (Site d))) :
    IsProbabilityMeasure ((bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b)) :=
  inferInstance


end Percolation
end StatMech
