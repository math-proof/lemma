/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexHalfFilledBetheContinuationPoint_parameter
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.1 = c₀ := rfl

theorem sixVertexHalfFilledBetheContinuationPoint_roots
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k).1.2 =
      sixVertexHalfFilledBetheRoots (ha.trans_le hc₀.1) k := by
  rfl

@[simp] theorem sixVertexHalfFilledBetheContinuationPoint_projection
    {a b c₀ : Real} (ha : 2 < a) (hc₀ : c₀ ∈ Set.Icc a b) (k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀ k) = ⟨c₀, hc₀⟩ :=
  rfl


theorem exists_sixVertexHalfFilledPerronSheet_of_densityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Ioo a b) (k : Nat)
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (hio : inner < outer)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFiniteDensityContinuumErrorOfLower t.1
            (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t.1
          (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi)
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho
        (sixVertexHalfFilledBetheContinuationPoint ha
          ⟨hc₀.1.le, hc₀.2.le⟩ k) < outer)
    (hbase : sixVertexSymmetricBetheEigenvalueValue c₀
        (sixVertexPositiveHalfBetheRoots (ha.trans hc₀.1) k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c₀)
    (hwave : sixVertexCoordinateBetheWave (N := sixVertexFourWidth 0 k) c₀
      (sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k) ≠ 0) :
    ∃ roots : C(Real, Fin ((k + 1) + (k + 1)) → Real),
      roots c₀ = sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k ∧
      (∀ t ∈ Set.Icc a b,
        SixVertexOpenRootSimplex (roots t) ∧
        SixVertexSatisfiesBetheEquations t (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (roots t)) ∧
      AnalyticOnNhd Real roots (Set.Ioo a b) ∧
      Set.EqOn
        (fun t => sixVertexSymmetricBetheEigenvalueKernel t
          (sixVertexEvenPositiveHalfProjection (k + 1) (roots t)))
        (sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega))
        (Set.Ioo a b) ∧
      ∀ t (ht : t ∈ Set.Icc a b),
        ∃ z : SixVertexBetheContinuationSpace a b
            (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)),
          sixVertexContinuationWeightedFiniteDensityGauge ha
              (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) rho z ≤ inner ∧
            z.1.1 = t ∧ z.1.2 = roots t := by
  let hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀.1.le, hc₀.2.le⟩
  let z₀ := sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k
  have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
  have hhalf : sixVertexFourWidth 0 k =
      2 * ((k + 1) + (k + 1)) := by
    unfold sixVertexFourWidth
    omega
  obtain ⟨roots, hroots₀, hrootsData, hrootsAnalytic, hrootsGauge⟩ :=
    exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_densityGauge
      ha hab hc₀Icc (by omega) hN hhalf rho hrhoEq hrhoMass
        hrhoLower hrho hio houter hinner hmargin z₀ hz₀g
        (sixVertexHalfFilledBetheContinuationPoint_projection ha hc₀Icc k)
  have hrootsSelected : roots c₀ =
      sixVertexHalfFilledBetheRoots (ha.trans hc₀.1) k := by
    rw [hroots₀]
    exact sixVertexHalfFilledBetheContinuationPoint_roots ha hc₀Icc k
  have hqbase : sixVertexEvenPositiveHalfProjection (k + 1) (roots c₀) =
      sixVertexPositiveHalfBetheRoots (ha.trans hc₀.1) k := by
    rw [hrootsSelected]
    rfl
  have hkernelBase : sixVertexSymmetricBetheEigenvalueKernel c₀
        (sixVertexEvenPositiveHalfProjection (k + 1) (roots c₀)) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c₀ := by
    rw [hqbase, sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · exact hbase
    · intro j
      exact ⟨sixVertexPositiveHalfBetheRoots_pos (ha.trans hc₀.1) k j,
        sixVertexPositiveHalfBetheRoots_lt_pi (ha.trans hc₀.1) k j⟩
  have hwaveRoots : sixVertexCoordinateBetheWave
      (N := sixVertexFourWidth 0 k) c₀ (roots c₀) ≠ 0 := by
    rwa [hrootsSelected]
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := sixVertexFourWidth 0 k) (m := k + 1) (by omega) (by
      unfold sixVertexFourWidth
      omega) isPreconnected_Ioo isOpen_Ioo
      (fun t ht => by change 2 < t; linarith [ht.1]) roots
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
      (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
      hrootsAnalytic hc₀ hwaveRoots hkernelBase
  exact ⟨roots, hrootsSelected, hrootsData, hrootsAnalytic, hperron, hrootsGauge⟩

end
end StatMech.FrontierD
