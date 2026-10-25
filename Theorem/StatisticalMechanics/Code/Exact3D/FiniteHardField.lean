/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.FiniteHardField
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem finiteFactorNumeratorSummand_tendsto {α : Type*}
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ) (a : α)
    (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => base a * factor H a * obs a)
      atTop
      (𝓝 (base a * limitFactor a * obs a)) := by
  have hmul :
      Tendsto (fun H : ℝ => (base a * obs a) * factor H a)
        atTop
        (𝓝 ((base a * obs a) * limitFactor a)) :=
    Filter.Tendsto.const_mul (base a * obs a) hfactor
  have hrewrite :
      (fun H : ℝ => base a * factor H a * obs a)
        =
      (fun H : ℝ => (base a * obs a) * factor H a) := by
    funext H
    ring
  have htarget : (base a * obs a) * limitFactor a =
      base a * limitFactor a * obs a := by
    ring
  simpa [hrewrite, htarget] using hmul


theorem finiteFactorDenominatorSummand_tendsto {α : Type*}
    (base limitFactor : α → ℝ) (factor : ℝ → α → ℝ) (a : α)
    (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => base a * factor H a)
      atTop
      (𝓝 (base a * limitFactor a)) :=
  Filter.Tendsto.const_mul (base a) hfactor


theorem finiteFactorNumerator_tendsto {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => finiteFactorNumerator s base obs factor H)
      atTop
      (𝓝 (finiteFactorLimitNumerator s base obs limitFactor)) := by
  unfold finiteFactorNumerator finiteFactorLimitNumerator
  exact tendsto_finsetSum s (fun a ha =>
    finiteFactorNumeratorSummand_tendsto base obs limitFactor factor a
      (hfactor a ha))


theorem finiteFactorDenominator_tendsto {α : Type*} (s : Finset α)
    (base limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => finiteFactorDenominator s base factor H)
      atTop
      (𝓝 (finiteFactorLimitDenominator s base limitFactor)) := by
  unfold finiteFactorDenominator finiteFactorLimitDenominator
  exact tendsto_finsetSum s (fun a ha =>
    finiteFactorDenominatorSummand_tendsto base limitFactor factor a
      (hfactor a ha))


theorem finiteFactorRatio_tendsto {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a)))
    (hden : finiteFactorLimitDenominator s base limitFactor ≠ 0) :
    Tendsto (fun H : ℝ => finiteFactorRatio s base obs factor H)
      atTop
      (𝓝 (finiteFactorLimitRatio s base obs limitFactor)) := by
  unfold finiteFactorRatio finiteFactorLimitRatio
  exact Filter.Tendsto.div
    (finiteFactorNumerator_tendsto s base obs limitFactor factor hfactor)
    (finiteFactorDenominator_tendsto s base limitFactor factor hfactor)
    hden


end Exact3D
end StatMech
