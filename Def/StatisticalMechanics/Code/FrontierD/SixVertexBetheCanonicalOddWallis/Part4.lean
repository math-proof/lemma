module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexOddWallisReferenceLogSum (m : Nat) : Real :=
  ∑ j ∈ Finset.range m,
    Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2))

end
end StatMech.FrontierD
