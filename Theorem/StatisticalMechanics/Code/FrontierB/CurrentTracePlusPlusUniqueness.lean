/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTracePlusPlusUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
open MeasureTheory


namespace StatMech.FrontierB

open ConfigSpace Lattice Percolation


theorem plusPlusSuperposedTraceLaw_uniqueness
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta) (hd : 1 ≤ d) :
    let mu := (independentSuperposedTraceLaw
      (infinitePlusCurrentMeasure d beta hbeta)
      (infinitePlusCurrentMeasure d beta hbeta) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  rcases hbeta.eq_or_lt with hzero | hpos
  · subst beta
    simpa only using plusPlusSuperposedTraceLaw_zero_beta_uniqueness d
  · exact plusPlusSuperposedTraceLaw_coarse_uniqueness d beta hpos hd
      (plusPlusSuperposedTraceLaw_isErgodic hd hpos)

end StatMech.FrontierB
