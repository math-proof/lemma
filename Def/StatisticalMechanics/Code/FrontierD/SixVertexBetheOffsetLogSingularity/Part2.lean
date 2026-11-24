module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogSingularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogNormSecondDerivativeBound (c : Real) : Real :=
  Real.pi ^ 2 *
      ((c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 +
        2 * (c ^ 2 - 1) ^ 2 / (c ^ 2 - 2) ^ 4) +
    Real.pi ^ 2 / 4

end
end StatMech.FrontierD
