/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexCentralWidthRate_eq_symmetricBetheRootAverage
    {c : ℝ} (hc : 2 < c) (roots : SixVertexSymmetricHalfFilledRoots)
    (hroots : SixVertexHasSymmetricBetheIdentification c roots) (k : ℕ) :
    sixVertexCentralWidthRate c k =
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c roots k := by
  rw [sixVertexCentralWidthRate, hroots k,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
  ring

theorem sixVertex_log_two_div_fourWidth_tendsto_zero :
    Tendsto (fun k : ℕ =>
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ)) atTop (nhds 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 / 4)).comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext k
  simp [sixVertexFourWidth]
  field_simp


theorem sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage
    {c a : ℝ} (hc : 2 < c) (roots : SixVertexSymmetricHalfFilledRoots)
    (hroots : SixVertexHasSymmetricBetheIdentification c roots) :
    Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) ↔
      Tendsto (sixVertexSymmetricBetheRootAverage c roots) atTop (nhds a) := by
  have heq : sixVertexCentralWidthRate c = fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c roots k := by
    funext k
    exact sixVertexCentralWidthRate_eq_symmetricBetheRootAverage
      hc roots hroots k
  rw [heq]
  constructor
  · intro h
    have hsub := h.sub sixVertex_log_two_div_fourWidth_tendsto_zero
    simpa using hsub
  · intro h
    simpa using sixVertex_log_two_div_fourWidth_tendsto_zero.add h


theorem sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    {N n : ℕ} (hn : n ≤ N) {c μ : ℝ} (hc : 0 < c)
    (v : SixVertexSector N n → ℝ) (hv : ∀ i, 0 < v i)
    (heig : sixVertexSectorTransfer N n c *ᵥ v = μ • v) :
    μ = sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  obtain ⟨u, hupos, hueig⟩ :=
    sixVertexSectorTop_exists_positive_eigenvector hn hc
  let A := sixVertexSectorTransfer N n c
  let top := sixVertexSectorTopEigenvalue N n hn c
  let S := ∑ i, u i * v i
  have hS : 0 < S := by
    apply Finset.sum_pos
    · intro i hi
      exact mul_pos (hupos i) (hv i)
    · exact Finset.univ_nonempty
  have hadj : ∑ i, u i * (A *ᵥ v) i =
      ∑ i, (A *ᵥ (fun i => u i)) i * v i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [show A j i = A i j by
      exact sixVertexTransfer_symmetric N c _ _]
    ring
  have hleft : ∑ i, u i * (A *ᵥ v) i = μ * S := by
    rw [show A *ᵥ v = μ • v from heig]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, u i * (μ * v i)) = ∑ i, μ * (u i * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = μ * ∑ i, u i * v i := by rw [Finset.mul_sum]
      _ = μ * S := rfl
  have hright : ∑ i, (A *ᵥ (fun i => u i)) i * v i = top * S := by
    rw [show A *ᵥ (fun i => u i) = top • (fun i => u i) from hueig]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, top * u i * v i) = ∑ i, top * (u i * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = top * ∑ i, u i * v i := by rw [Finset.mul_sum]
      _ = top * S := rfl
  rw [hleft, hright] at hadj
  nlinarith

end StatMech.FrontierD
