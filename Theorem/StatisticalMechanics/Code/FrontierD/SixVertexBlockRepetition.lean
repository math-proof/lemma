/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
open Finset


namespace StatMech.FrontierD

@[simp] theorem finProdFinEquiv_divNat {m n : ℕ}
    (x : Fin m) (i : Fin n) :
    (finProdFinEquiv (x, i)).divNat = x := by
  have h := (finProdFinEquiv (m := m) (n := n)).symm_apply_apply (x, i)
  simpa only [finProdFinEquiv_symm_apply] using congrArg Prod.fst h

@[simp] theorem finProdFinEquiv_modNat {m n : ℕ}
    (x : Fin m) (i : Fin n) :
    (finProdFinEquiv (x, i)).modNat = i := by
  have h := (finProdFinEquiv (m := m) (n := n)).symm_apply_apply (x, i)
  simpa only [finProdFinEquiv_symm_apply] using congrArg Prod.snd h


end StatMech.FrontierD
