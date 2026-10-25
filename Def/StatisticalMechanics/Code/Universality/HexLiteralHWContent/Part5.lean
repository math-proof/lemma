/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HexHWContentDecomp

variable {D : Type}


section Finite

variable [Fintype D]


noncomputable def lowerImage (H : HexHWContentDecomp D) : Finset HexHWContentHalf :=
  by
    classical
    exact Finset.univ.image H.lower


noncomputable def upperImage (H : HexHWContentDecomp D) : Finset HexHWContentHalf :=
  by
    classical
    exact Finset.univ.image H.upper


noncomputable def pairImage (H : HexHWContentDecomp D) :
    Finset (HexHWContentHalf × HexHWContentHalf) :=
  by
    classical
    exact Finset.univ.image H.pair


end Finite
end HexHWContentDecomp
end StatMech.Universality
