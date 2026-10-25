/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part8


namespace StatMech.Universality

open HexWalk


noncomputable def hlha_reverseAugment (ts : List ℤ) : List ℤ :=
  match ts with
  | [] => hlha_emptyAugment
  | _ :: us =>
      let r := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts
      hlha_augmentSide (hlha_negCoord r.dir) (loopReverse us)

end StatMech.Universality
