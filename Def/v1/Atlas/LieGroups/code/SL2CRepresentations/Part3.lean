/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
public import Theorem.Nat.basisHC.eq.SMul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Inductive.v1.Atlas.LieGroups.code.SL2CRepresentations

@[expose] public section

noncomputable section

open Complex

open scoped Classical

attribute [instance] SL2C_UnitaryRep.instNACG
  SL2C_UnitaryRep.instIPS SL2C_UnitaryRep.instCS

def SL2C_IrredAdmissible.kTypes : SL2C_IrredAdmissible → Set ℕ
  | .finiteDim n => {n}
  | .principalSeries lam mu _ =>
      {j | ∃ k : ℕ, ∃ n : ℤ, mu - lam = (n : ℂ) ∧ j = Int.natAbs n + 2 * k}

end
