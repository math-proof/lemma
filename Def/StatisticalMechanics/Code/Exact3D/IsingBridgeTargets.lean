/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria


namespace StatMech

namespace Exact3D

noncomputable def Ising3DFreeModel : CriticalModel Ising3DSite where
  betaC := Ising.betaC 3
  twoPoint := ising3DFreeTwoPoint


def PlusFreeTwoPointAgreeBelowBetaC : Prop :=
  ∀ β, β < Ising.betaC 3 →
    ∀ x y : Ising3DSite, ising3DPlusTwoPoint β x y = ising3DFreeTwoPoint β x y


def PlusXAxisExactExponentialDecay (β A m : ℝ) : Prop :=
  ∀ᶠ n in Filter.atTop,
    |twoPointOnXAxis β n| = A * Real.exp (-(m * (n : ℝ)))


def FreeXAxisExactExponentialDecay (β A m : ℝ) : Prop :=
  ∀ᶠ n in Filter.atTop,
    |freeTwoPointOnXAxis β n| = A * Real.exp (-(m * (n : ℝ)))


def PlusXAxisSubexponentialPrefactorDecay (β : ℝ) (A : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < A n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    ∀ᶠ n in Filter.atTop,
      |twoPointOnXAxis β n| = A n * Real.exp (-(m * (n : ℝ)))


def FreeXAxisSubexponentialPrefactorDecay (β : ℝ) (A : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < A n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    ∀ᶠ n in Filter.atTop,
      |freeTwoPointOnXAxis β n| = A n * Real.exp (-(m * (n : ℝ)))


def PlusXAxisTwoSidedSubexponentialBounds
    (β : ℝ) (Alo Ahi : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < Alo n) ∧
    (∀ᶠ n in Filter.atTop, 0 < Ahi n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ᶠ n in Filter.atTop,
      Alo n * Real.exp (-(m * (n : ℝ))) ≤ |twoPointOnXAxis β n|) ∧
    ∀ᶠ n in Filter.atTop,
      |twoPointOnXAxis β n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))


def FreeXAxisTwoSidedSubexponentialBounds
    (β : ℝ) (Alo Ahi : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < Alo n) ∧
    (∀ᶠ n in Filter.atTop, 0 < Ahi n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ᶠ n in Filter.atTop,
      Alo n * Real.exp (-(m * (n : ℝ))) ≤ |freeTwoPointOnXAxis β n|) ∧
    ∀ᶠ n in Filter.atTop,
      |freeTwoPointOnXAxis β n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))


def PlusXAxisFKConnectionAgrees (β : ℝ) (conn : ℕ → ℝ) : Prop :=
  ∀ᶠ n in Filter.atTop, |twoPointOnXAxis β n| = conn n


def FreeXAxisFKConnectionAgrees (β : ℝ) (conn : ℕ → ℝ) : Prop :=
  ∀ᶠ n in Filter.atTop, |freeTwoPointOnXAxis β n| = conn n


end Exact3D
end StatMech
