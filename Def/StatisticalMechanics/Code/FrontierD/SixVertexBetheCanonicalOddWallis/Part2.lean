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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexBetheDesingularizedLogObservable (c x : Real) : Real :=
  let a := c ^ 2 - 1
  (1 / 2 : Real) * Real.log (a ^ 2 + 1 + 2 * a * Real.cos x) -
    Real.log (Real.sinc (x / 2))

end
end StatMech.FrontierD
