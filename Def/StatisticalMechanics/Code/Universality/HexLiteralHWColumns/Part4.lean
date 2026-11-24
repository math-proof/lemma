module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
public import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWColumns


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def HLHCCanonicalColumnWalk.stripHeight
    {T : ℕ} {ts : List ℤ} (W : HLHCCanonicalColumnWalk T ts) : ℕ :=
  max ((Finset.range ts.length).sup
      (fun k => hlhc_coordBound (hlhc_prefixCoord ts W.legal.1 k)))
    (hlhc_coordBound W.topCoord)

end
end StatMech.Universality
