/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Structure.v1.Atlas.LieGroups.code.SL2CRepresentations.Part2


noncomputable section

open Complex

open scoped Classical

attribute [instance] SL2C_UnitaryRep.instNACG
  SL2C_UnitaryRep.instIPS SL2C_UnitaryRep.instCS

def HCBimoduleParam.Equiv (ξ₁ ξ₂ : HCBimoduleParam) : Prop :=
  (ξ₁.mu = ξ₂.mu ∧ ξ₁.lam = ξ₂.lam) ∨
  (ξ₁.mu = -ξ₂.mu ∧ ξ₁.lam = -ξ₂.lam)

def HCBimoduleParam.neg (ξ : HCBimoduleParam) : HCBimoduleParam where
  mu := -ξ.mu
  lam := -ξ.lam
  diff_is_int := by
    obtain ⟨n, hn⟩ := ξ.diff_is_int
    exact ⟨-n, by push_cast; linear_combination -hn⟩

def HCBimoduleParam.IsSameSignNonzeroIntegers (ξ : HCBimoduleParam) : Prop :=
  ∃ (n m : ℤ), n ≠ 0 ∧ m ≠ 0 ∧ (0 < n ∧ 0 < m ∨ n < 0 ∧ m < 0) ∧
    ξ.lam = (n : ℂ) ∧ ξ.mu = (m : ℂ)

def principalSeriesKTypes (k : ℤ) : Set ℕ :=
  {j : ℕ | ∃ i : ℕ, j = Int.natAbs k + 2 * i}

def IsHermitianPS (lam mu : ℂ) : Prop :=
  lam ^ 2 = starRingEnd ℂ mu ^ 2

end
