/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part8
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


noncomputable def frpPhi (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) : ℝ :=
  ∑ q ∈ frpBoundaryPairs K S,
    (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
      (frpMeasure K beta).real
        (connEvent (frpGraph K) (S : Set (Site d)) (0 : Site d) {q.1})


def frpCrossingEvent (K : FiniteRangeKernel d) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  connEvent (frpGraph K) Set.univ (0 : Site d) (box d (n - 1))ᶜ

noncomputable def frpCrossProb (K : FiniteRangeKernel d) (beta : ℝ)
    (n : ℕ) : ℝ :=
  (frpMeasure K beta).real (frpCrossingEvent K n)


end Sharpness
end StatMech
