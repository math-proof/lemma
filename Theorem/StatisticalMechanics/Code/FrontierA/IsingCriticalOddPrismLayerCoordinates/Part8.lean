/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part8


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem spin_oddPrismBlockConfigEquiv_lower
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n))
    (v : OddPrismLowerBlockSite n) :
    spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin a v := by
  unfold spin
  congr 1
  unfold oddPrismBlockConfigEquiv
  simp only [Equiv.trans_apply, isingCfgEquiv, Equiv.coe_fn_symm_mk]
  rw [show (StatMech.FK.agl_sumEquiv
      (oddPrismAtOrBelowCenter n)).symm v.1 = Sum.inl v by
    exact Equiv.sumCompl_symm_apply_of_pos v.2]
  have h := isingSumConfigEquiv.apply_symm_apply (a, b)
  exact congrArg (fun x : Bool => x = true)
    (congrFun (congrArg Prod.fst h) v)

@[simp] theorem spin_oddPrismBlockConfigEquiv_upper
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n))
    (v : OddPrismUpperBlockSite n) :
    spin (oddPrismBlockConfigEquiv n (a, b)) v.1 = spin b v := by
  unfold spin
  congr 1
  unfold oddPrismBlockConfigEquiv
  simp only [Equiv.trans_apply, isingCfgEquiv, Equiv.coe_fn_symm_mk]
  rw [show (StatMech.FK.agl_sumEquiv
      (oddPrismAtOrBelowCenter n)).symm v.1 = Sum.inr v by
    exact Equiv.sumCompl_symm_apply_of_neg v.2]
  have h := isingSumConfigEquiv.apply_symm_apply (a, b)
  exact congrArg (fun x : Bool => x = true)
    (congrFun (congrArg Prod.snd h) v)


end
end StatMech.FrontierA
