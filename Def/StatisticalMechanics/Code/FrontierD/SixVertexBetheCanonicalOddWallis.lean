/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexOddWallisHalfProduct (m : Nat) : Real :=
  ∏ j ∈ Finset.range m, ((2 * j + 1 : Nat) : Real) / (2 * j + 2)

end
end StatMech.FrontierD
