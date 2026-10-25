/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

def kappaSquare (p0 p1 : ℝ) : ℝ := p0 + p1 - 1


def kappaTri (p0 p1 p2 : ℝ) : ℝ := p0 + p1 + p2 - p0 * p1 * p2 - 1


def kappaHex (p0 p1 p2 : ℝ) : ℝ := -kappaTri (1 - p0) (1 - p1) (1 - p2)


def IsCriticalSquare (p0 p1 : ℝ) : Prop := kappaSquare p0 p1 = 0


def IsCriticalTri (p0 p1 p2 : ℝ) : Prop := kappaTri p0 p1 p2 = 0


def IsCriticalHex (p0 p1 p2 : ℝ) : Prop := kappaHex p0 p1 p2 = 0


end Universality
end StatMech
