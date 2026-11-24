module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability
open scoped Real
open MeasureTheory Interval


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

noncomputable def ons_criticalLogBound (y : ℝ) : ℝ :=
  Real.log 9 + Real.log 2 + |Real.log (1 - Real.cos y)|

end StatMech.Onsager
