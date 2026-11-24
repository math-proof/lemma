module
public import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk


noncomputable def hlha_prefixReverseData (ts : List ℤ) :
    Option (HexReturnCoord × List ℤ) :=
  match ts.take (hexW2_cutPos 0 ts) with
  | [] => none
  | _ :: us =>
      let r := hlha_cutState ts
      some (hlha_negCoord r.dir, loopReverse us)

noncomputable def hlha_prefixAugment (ts : List ℤ) : List ℤ :=
  match hlha_prefixReverseData ts with
  | none => hlha_emptyAugment
  | some (d, us) => hlha_augmentSide d us

end StatMech.Universality
