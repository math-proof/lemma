/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangNormalFamilyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangThermodynamicPrereq.Part2
open Filter Set Topology


namespace StatMech.FrontierA

def IsLocallyUniformlySequentiallyPrecompact
    (F : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) g atTop U


end StatMech.FrontierA
