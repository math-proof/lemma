/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Def.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part3
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem rss_dual_reflected_halfWiredBoundary (e : rss_StripEnd) :
    RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) =
      rss_halfWiredBoundary e := by
  cases e <;> rfl


end Universality
end StatMech
