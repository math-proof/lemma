/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferFailedGate
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferNormalization
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalTransferSymmDiff_eq_rowSymmDiff_of_normalRows
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c d : ↑m -> Fin 4)
    (hac : canonicalNormalRow ends m k zero a =
      canonicalNormalRow ends m k zero c)
    (hbd : canonicalNormalRow ends m k zero b =
      canonicalNormalRow ends m k zero d)
    (hrow : rowClass m c 0 ∆ rowClass m d 0 =
      canonicalTransferUnion ends m k zero a ∆
        canonicalTransferUnion ends m k zero b) :
    canonicalTransferUnion ends m k zero c ∆
        canonicalTransferUnion ends m k zero d =
      rowClass m a 0 ∆ rowClass m b 0 := by
  let Ra := rowClass m a 0
  let Rb := rowClass m b 0
  let Rc := rowClass m c 0
  let Rd := rowClass m d 0
  let Ta := canonicalTransferUnion ends m k zero a
  let Tb := canonicalTransferUnion ends m k zero b
  let Tc := canonicalTransferUnion ends m k zero c
  let Td := canonicalTransferUnion ends m k zero d
  change Ra ∆ Ta = Rc ∆ Tc at hac
  change Rb ∆ Tb = Rd ∆ Td at hbd
  change Rc ∆ Rd = Ta ∆ Tb at hrow
  change Tc ∆ Td = Ra ∆ Rb
  calc
    Tc ∆ Td = (Tc ∆ Td) ∆ (Rc ∆ Rc) ∆ (Rd ∆ Rd) := by simp
    _ = (Rc ∆ Tc) ∆ (Rd ∆ Td) ∆ Rc ∆ Rd := by ac_rfl
    _ = (Ra ∆ Ta) ∆ (Rb ∆ Tb) ∆ Rc ∆ Rd := by rw [← hac, ← hbd]
    _ = (Ra ∆ Rb) ∆ (Ta ∆ Tb) ∆ (Rc ∆ Rd) := by ac_rfl
    _ = (Ra ∆ Rb) ∆ (Rc ∆ Rd) ∆ (Rc ∆ Rd) := by rw [← hrow]
    _ = Ra ∆ Rb := by simp [symmDiff_assoc]

end StatMech.GrahamGHS.FourColor
