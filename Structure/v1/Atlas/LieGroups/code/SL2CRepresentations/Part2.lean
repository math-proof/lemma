/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
public import Lemma.Nat.basisHC.eq.SMul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Def.v1.Atlas.LieGroups.code.SL2CRepresentations


public noncomputable section

open Complex

open scoped Classical

attribute [instance] SL2C_UnitaryRep.instNACG
  SL2C_UnitaryRep.instIPS SL2C_UnitaryRep.instCS

structure PSActionBundle where
  action : ℤ → ℝ → SL2C →* (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
  symm : ∀ m t, action m t = action (-m) (-t)

structure CSActionBundle where
  action : (s : ℝ) → (-1 : ℝ) < s → s < 1 →
    SL2C →* (lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
  symm : ∀ (s : ℝ) (hs1 : (-1 : ℝ) < s) (hs2 : s < 1)
    (hs1' : (-1 : ℝ) < -s) (hs2' : -s < 1),
    action s hs1 hs2 = action (-s) hs1' hs2'

structure HCBimoduleParam where
  mu : ℂ
  lam : ℂ
  diff_is_int : ∃ n : ℤ, lam - mu = (n : ℂ)

end
