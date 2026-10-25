/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


theorem finiteIsingXAxisTwoPointInVolume_eq_of_le
    {β : ℝ} {N n : ℕ} (hn : n ≤ N) :
    finiteIsingXAxisTwoPointInVolume β N n =
      finiteIsingXAxisTwoPointInBox β N n hn := by
  simp [finiteIsingXAxisTwoPointInVolume, hn]


theorem finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2
    (d N : ℕ) (β : ℝ)
    (hp : 0 < IsingFK.pOfBeta β) (hp1 : IsingFK.pOfBeta β < 1)
    (x y : boxVerts d N) :
    (∑ σ : ConfigSpace (boxVerts d N),
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y)) =
      (freeFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y) := by
  have hspin : ∀ σ : boxVerts d N → Fin 2,
      Ising.spin (IsingFK.toIsing σ) x * Ising.spin (IsingFK.toIsing σ) y =
        isingSpin (σ x) * isingSpin (σ y) := by
    intro σ
    rw [← Ising.bond_mk]
    rw [IsingFK.bond_eq_two_mul_ite]
    rw [isingSpin_mul]
    by_cases h : σ x = σ y
    · rw [if_pos h, if_pos ((IsingFK.sigma_eq_iff σ x y).mp h)]
    · rw [if_neg h, if_neg (fun ht =>
        h ((IsingFK.sigma_eq_iff σ x y).mpr ht))]
  have hesFirst :
      (∑ σ : boxVerts d N → Fin 2,
          esFirstMarginal (boxGraph d N) 2 (IsingFK.pOfBeta β) σ *
            (isingSpin (σ x) * isingSpin (σ y))) =
        esTwoPoint (boxGraph d N) (IsingFK.pOfBeta β) x y := by
    unfold esFirstMarginal esTwoPoint
    simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
  rw [freeFiniteMeasure_real_boxConnEvent d N hp hp1
    (by norm_num : (0 : ℝ) < 2) x y]
  rw [← (Equiv.ofBijective (IsingFK.toIsing (V := boxVerts d N))
    IsingFK.toIsing_bijective).sum_comp
      (fun σ : ConfigSpace (boxVerts d N) =>
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y))]
  change (∑ σ : boxVerts d N → Fin 2,
      Ising.isingProb (boxGraph d N) β 0 (IsingFK.toIsing σ) *
        (Ising.spin (IsingFK.toIsing σ) x *
          Ising.spin (IsingFK.toIsing σ) y)) =
    twoPointFun (boxGraph d N) (IsingFK.pOfBeta β) 2 x y
  simp_rw [hspin]
  have hprob : ∀ σ : boxVerts d N → Fin 2,
      Ising.isingProb (boxGraph d N) β 0 (IsingFK.toIsing σ) =
        esFirstMarginal (boxGraph d N) 2 (IsingFK.pOfBeta β) σ := by
    intro σ
    rw [IsingFK.isingProb_eq_pottsProb
      (boxGraph d N) β (2 * β) 1 (by ring) σ]
    rw [← esFirstMarginal_eq_pottsProb (boxGraph d N) 2 (2 * β) 1 σ]
    simp [IsingFK.pOfBeta]
  simp_rw [hprob]
  rw [hesFirst, esTwoPoint_eq_connProb]
  simpa [connProb, Connected, connEvent] using
    (twoPointFun_eq_sum_filter
      (boxGraph d N) (IsingFK.pOfBeta β) (2 : ℝ) x y).symm


theorem finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
    (d N : ℕ) {β : ℝ} (hβ : 0 < β) (x y : boxVerts d N) :
    (∑ σ : ConfigSpace (boxVerts d N),
        Ising.isingProb (boxGraph d N) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y)) =
      (freeFiniteMeasure d N (Ising.pOfBeta_pos hβ)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real
          (boxConnEvent d N x y) :=
  finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_q2
    d N β (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) x y


theorem finiteIsingXAxisTwoPointBox_eq_freeFiniteVolumeXAxisConnectionQ2
    {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    finiteIsingXAxisTwoPointBox β n =
      freeFiniteVolumeXAxisConnectionQ2 (IsingFK.pOfBeta β)
        (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β) n := by
  unfold finiteIsingXAxisTwoPointBox freeFiniteVolumeXAxisConnectionQ2
  exact finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
    3 n hβ (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)


theorem finiteIsingXAxisTwoPointInVolume_eq_freeFiniteVolumeFullConnectionQ2
    {β : ℝ} (hβ : 0 < β) (N n : ℕ) :
    finiteIsingXAxisTwoPointInVolume β N n =
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume β hβ N n := by
  by_cases hn : n ≤ N
  · rw [finiteIsingXAxisTwoPointInVolume_eq_of_le hn]
    unfold freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume
    rw [dif_pos hn]
    unfold finiteIsingXAxisTwoPointInBox
    exact finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
      3 N hβ (ising3DOriginBoxVertex N)
      (ising3DXAxisBoxVertexInBox N n hn)
  · simp [finiteIsingXAxisTwoPointInVolume,
      freeFiniteVolumeXAxisFullConnectionOfBetaQ2InVolume, hn]


end Exact3D
end StatMech
