/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


noncomputable def leftMaskReference (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) : ↑m -> Fin 4 :=
  if h : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c then
    Classical.choose
      (exists_minimal_leftMaskCandidate ends m j k l zero p h)
  else
    fun _ => 0

end StatMech.GrahamGHS.FourColor
