/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part6


namespace StatMech.Universality

open HexWalk


noncomputable def hlha_cutState (ts : List ℤ) : HLHRCoordRun :=
  hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take (hexW2_cutPos 0 ts))

noncomputable def hlha_suffixAugment (ts : List ℤ) : List ℤ :=
  match ts.drop (hexW2_cutPos 0 ts) with
  | [] => hlha_emptyAugment
  | t :: us => hlha_augmentSide ((hlha_cutState ts).dir.turn t) us

end StatMech.Universality
