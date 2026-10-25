/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def emptyBoundarySector
    (ends : I → Sym2 W) (S : Finset I) : boundarySector ends S ∅ := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simp [sources, degK]


noncomputable def emptyMaskCyclePair
    (ends : I → Sym2 W) (p : Finset I × Finset I) :
    boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ :=
  (emptyBoundarySector ends p.1, emptyBoundarySector ends p.2)


end StatMech.GrahamGHS.FourColor
