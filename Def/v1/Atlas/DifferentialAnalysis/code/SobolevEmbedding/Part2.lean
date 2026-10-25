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
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

/-- Partial derivative `∂_j u` as an element of `H^{m-1}`, given `u ∈ H^m`. -/
def SobolevSpace.partialDeriv {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) : SobolevSpace n (m - 1) where
  toFun := fun x => fderiv ℝ u.toFun x (EuclideanSpace.single j 1)
  contDiff_toFun := by
    have hle : ((↑(m - 1) : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((↑m : ℕ∞) : WithTop ℕ∞) := by
      norm_cast; exact (Nat.sub_add_cancel hm).le
    exact (ContDiff.fderiv_right u.contDiff_toFun hle).clm_apply contDiff_const
  iteratedFDeriv_memLp i hi := partialDeriv_iteratedFDeriv_memLp hm u j i hi


set_option synthInstance.maxHeartbeats 80000 in

/-- Iterate the partial derivative in direction `j` exactly `k` times, mapping
`H^m` into `H^{m-k}`. -/
def SobolevSpace.iteratedPartialDeriv {n : ℕ} {m : ℕ}
    (j : Fin n) : (k : ℕ) → (hk : k ≤ m) → SobolevSpace n m → SobolevSpace n (m - k)
  | 0, _, u => u.toLowerOrder (by omega)
  | k + 1, hk, u =>
    let v := SobolevSpace.iteratedPartialDeriv j k (by omega) u
    (v.partialDeriv (by omega) j).toLowerOrder (by omega)

end SobolevEmbedding
end
