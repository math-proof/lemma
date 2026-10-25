/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def invariantMiddleTransfer (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (k : W) : Finset I :=
  edgeComponent ends (middleMask m c) k


noncomputable def invariantOuterTransfer (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (j zero : W) : Finset I :=
  if connK ends (outerMask m c) zero j then ∅
  else edgeComponent ends (outerMask m c) zero

noncomputable def invariantComponentSelector (ends : I -> Sym2 W)
    (m : Finset I) (j k zero : W) (c : ↑m -> Fin 4) :
    Finset I × Finset I :=
  (invariantMiddleTransfer ends m c k,
    invariantOuterTransfer ends m c j zero)

end StatMech.GrahamGHS.FourColor
