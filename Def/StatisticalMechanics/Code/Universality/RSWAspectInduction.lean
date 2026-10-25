/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAspectInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConstantMaintenance
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

variable (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]


noncomputable def rai_cross (n : ℤ) (k : ℕ) : ℝ :=
  μ.real (horizontalCrossingEvent 0 ((k : ℤ) * n) 0 n)

end Universality
end StatMech
