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
import Inductive.v1.Atlas.LieGroups.code.SL2CRepresentations


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
