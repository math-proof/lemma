/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


def rss_faceStrip (n : ℤ) : Set (Site 2) :=
  {x | -n ≤ x 1 ∧ x 1 ≤ 3 * n - 1}


def rss_bottomFaceLine (n : ℤ) : Set (Site 2) := {x | x 1 = -n}


def rss_topFaceLine (n : ℤ) : Set (Site 2) := {x | x 1 = 3 * n - 1}


end Universality
end StatMech
