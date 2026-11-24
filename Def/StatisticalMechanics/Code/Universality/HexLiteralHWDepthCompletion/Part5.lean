module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
public import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def HLHDAEndpointColumnWalk.stripHeight
    {T : ℕ} {ts : List ℤ} (W : HLHDAEndpointColumnWalk T ts) : ℕ :=
  max ((Finset.range ts.length).sup
      (fun k => hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 k)))
    (hlhc_coordBound W.topCoord)

end
end StatMech.Universality
