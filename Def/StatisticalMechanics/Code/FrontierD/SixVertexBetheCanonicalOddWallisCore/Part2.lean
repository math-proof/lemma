/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Mathlib.Analysis.Real.Pi.Wallis
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexIdealWallisLogCorrection (n : Nat) : Real :=
  -Real.log (Real.Wallis.W n)

end
end StatMech.FrontierD
