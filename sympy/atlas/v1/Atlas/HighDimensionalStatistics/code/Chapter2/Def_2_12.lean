/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset Matrix BigOperators

namespace Rigollet

/-- `ℓ_0` "norm" of a vector: the number of nonzero coordinates. -/
noncomputable def l0norm {d : ℕ} (θ : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun j => θ j ≠ 0)).card

/-- `ℓ_1` norm of a vector: the sum of absolute values of its coordinates. -/
noncomputable def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, |θ j|

/-- Squared Euclidean norm of a vector: `∑_i v_i²`. -/
noncomputable def sqL2norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- **BIC estimator** (Definition 2.12): a minimiser of the penalised criterion
`(1/n) · ‖Y - Xθ‖² + τ² · ‖θ‖_0`. -/
def IsBICEstimator {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  0 < τ ∧ ∀ θ : Fin d → ℝ,
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θhat) + τ^2 * (l0norm θhat : ℝ) ≤
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θ) + τ^2 * (l0norm θ : ℝ)

/-- **Lasso estimator** (Definition 2.12): a minimiser of the penalised criterion
`(1/n) · ‖Y - Xθ‖² + 2τ · ‖θ‖_1`. -/
def IsLassoEstimator {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  0 < τ ∧ ∀ θ : Fin d → ℝ,
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θhat) + 2 * τ * l1norm θhat ≤
    (1 / (n : ℝ)) * sqL2norm (Y - X.mulVec θ) + 2 * τ * l1norm θ

/-- Alias for `IsBICEstimator`, emphasising the squared-`ℓ_2` data-fitting term. -/
abbrev IsBICEstimatorL2 {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  IsBICEstimator X Y τ θhat

/-- Alias for `IsLassoEstimator`, emphasising the squared-`ℓ_2` data-fitting term. -/
abbrev IsLassoEstimatorL2 {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  IsLassoEstimator X Y τ θhat

end Rigollet
