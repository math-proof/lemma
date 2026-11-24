module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part2


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

def sixVertexSincDerivative (x : Real) : Real :=
  if x = 0 then 0 else (x * Real.cos x - Real.sin x) / x ^ 2

end
end StatMech.FrontierD
