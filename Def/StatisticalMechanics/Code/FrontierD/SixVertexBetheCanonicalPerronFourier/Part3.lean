/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityCompact : TopologicalSpace.Compacts Real :=
  ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩

def sixVertexAbelLogTermMulRootDensityContinuous
    {lam : Real} (hlam : 0 < lam) (r : Real) (n : Nat) : C(Real, Real) :=
  ⟨fun alpha =>
      (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
        (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha,
    (by
      apply Continuous.mul
      · fun_prop
      · exact continuous_sixVertexFourierRootDensity hlam)⟩

end
end StatMech.FrontierD
