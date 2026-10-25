/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hemb : CanonicalMaskRightEdgePreimageEmbedding
      ends m j k l zero p) :
    CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p := by
  classical
  intro c q hqc
  obtain ⟨f⟩ := hemb c q hqc
  have hcard := Fintype.card_le_of_embedding f
  simpa only [canonicalMaskRightRightDegree,
    canonicalMaskRightLeftDegree] using hcard


end StatMech.GrahamGHS.FourColor
