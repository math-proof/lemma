module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
public import Mathlib.Analysis.Real.Pi.Wallis


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBethePrefactor c
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
      (sixVertexOddCentralIndex (s + k + 1)) /
    (sixVertexFourWidth (2 * s + 1) k : Real)

end
end StatMech.FrontierD
