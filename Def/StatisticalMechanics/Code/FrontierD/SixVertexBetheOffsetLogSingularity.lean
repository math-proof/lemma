/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogNormKernel (c x : Real) : Real :=
  let a := c ^ 2 - 1
  (1 / 2 : Real) *
    (Real.log (a ^ 2 + 1 + 2 * a * Real.cos x) -
      Real.log (2 - 2 * Real.cos x))

def sixVertexBetheLogNormDerivative (c x : Real) : Real :=
  let a := c ^ 2 - 1
  (-a * Real.sin x / (a ^ 2 + 1 + 2 * a * Real.cos x)) -
    Real.sin x / (2 - 2 * Real.cos x)

end
end StatMech.FrontierD
