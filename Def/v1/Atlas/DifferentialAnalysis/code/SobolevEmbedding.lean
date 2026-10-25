/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Instance.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- `H^m ⊂ H^{m'}` whenever `m' ≤ m`: lower the Sobolev order of an element by
restricting the derivative-integrability hypothesis. -/
def SobolevSpace.toLowerOrder {n : ℕ} {m m' : ℕ} (hle : m' ≤ m)
    (u : SobolevSpace n m) : SobolevSpace n m' where
  toFun := u.toFun
  contDiff_toFun := u.contDiff_toFun.of_le (Nat.cast_le.mpr hle)
  iteratedFDeriv_memLp j hj := u.iteratedFDeriv_memLp j (le_trans hj hle)


end SobolevEmbedding
end
