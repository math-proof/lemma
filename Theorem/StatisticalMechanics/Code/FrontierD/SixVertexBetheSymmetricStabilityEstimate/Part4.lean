/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part3


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexContinuationWeightedFiniteDensityGauge
    {a b : Real} (ha : 2 < a) (N n : Nat)
    (rho : C(Set.Icc a b × Real, Real)) :
    Continuous
      (sixVertexContinuationWeightedFiniteDensityGauge ha N n rho) := by
  let X := SixVertexBetheContinuationSpace a b N n
  let K := Set.Icc (-Real.pi) Real.pi
  have hweight : Continuous (fun zx : X × K =>
      sixVertexRootDensityWeight zx.1.1.1 zx.2.1) := by
    unfold sixVertexRootDensityWeight
    apply Continuous.div
    · unfold sixVertexBetheIntegratingFactor sixVertexDelta
      fun_prop
    · unfold sixVertexRootDensityScale sixVertexAnisotropyMagnitude
        sixVertexDelta
      fun_prop
    · intro zx
      exact (sixVertexRootDensityScale_pos
        (ha.trans_le zx.1.2.1.1)).ne'
  have hfinite : Continuous (fun zx : X × K =>
      sixVertexFiniteRootDensity zx.1.1.1 N n zx.1.1.2 zx.2.1) := by
    unfold sixVertexFiniteRootDensity
    apply Continuous.div_const
    apply Continuous.add continuous_const
    apply Continuous.div_const
    apply continuous_finsetSum
    intro k _
    apply Continuous.div
    · simp only [sixVertexDelta, sixVertexBetheIntegratingFactor]
      fun_prop
    · simp only [sixVertexThetaDerivativeDenominator,
        sixVertexThetaDenominator, sixVertexDelta]
      fun_prop
    · intro zx
      exact (sixVertexThetaDerivativeDenominator_pos
        (ha.trans_le zx.1.2.1.1) zx.2.1 (zx.1.1.2 k)).ne'
  have hrho : Continuous (fun zx : X × K =>
      rho (⟨zx.1.1.1, zx.1.2.1⟩, zx.2.1)) := by
    fun_prop
  have huncurry : Continuous (fun zx : X × K =>
      sixVertexRootDensityWeight zx.1.1.1 zx.2.1 *
        (sixVertexFiniteRootDensity zx.1.1.1 N n zx.1.1.2 zx.2.1 -
          rho (⟨zx.1.1.1, zx.1.2.1⟩, zx.2.1))) :=
    hweight.mul (hfinite.sub hrho)
  have hmap : Continuous (fun z : X =>
      sixVertexWeightedFiniteDensityDifference (ha.trans_le z.2.1.1)
        N n z.1.2 (sixVertexContinuumDensitySection rho z)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    simpa only [sixVertexWeightedFiniteDensityDifference,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply,
      ContinuousMap.coe_mk] using huncurry
  exact continuous_norm.comp hmap

theorem sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus
    {a b : Real} (ha : 2 < a) {N n r : Nat} (hN : 0 < N)
    (hr : r = n + 1)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    (rho : C(Set.Icc a b × Real, Real))
    (hrhoEq : ∀ t : Set.Icc a b,
      SixVertexSatisfiesContinuousDensityEquation t.1
        (sixVertexContinuumDensityAt rho t))
    (hrhoMass : ∀ t : Set.Icc a b,
      ∫ y in -Real.pi..Real.pi, sixVertexContinuumDensityAt rho t y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hinner : ∀ t : Set.Icc a b,
      sixVertexRootDensityContractionRate t.1 * outer +
          sixVertexFiniteDensityContinuumErrorOfLower
            t.1 N (rhoLower / 2) ≤ inner) :
    ∀ z : SixVertexBetheContinuationSpace a b N r,
      ¬(inner <
          sixVertexContinuationWeightedFiniteDensityGauge
            ha N r rho z ∧
        sixVertexContinuationWeightedFiniteDensityGauge
            ha N r rho z < outer) := by
  subst r
  intro z
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have htwo : 2 * (n + 1) ≤ N := by omega
  have hopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha htwo z.2
  have hsol : SixVertexSatisfiesBetheEquations
      z.1.1 N (n + 1) z.1.2 :=
    (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
    sixVertexContinuumDensitySection, t] using
    sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus
      hc hN hcount hhalf hopen hsol
      (sixVertexContinuumDensityAt rho t) (hrhoEq t) (hrhoMass t)
      hrhoLower (hrho t) (houter t) (hinner t)

theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {rho : Real → Real} {rhoLower eta : Real}
    (hrhoLower : 0 < rhoLower)
    (hrho : ∀ x, rhoLower ≤ rho x)
    (heta : eta ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N (m + m)
          (sixVertexEvenSymmetricLift m q) x - rho x)| ≤ eta)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N
        (rhoLower / 2) < 2 * Real.pi) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hdensityHalf : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N (m + m)
        (sixVertexEvenSymmetricLift m q) x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N (m + m)
        (sixVertexEvenSymmetricLift m q)).exists_mem_Ioc
          (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc
          y ≤ -Real.pi + 2 * Real.pi := hy.2
          _ = Real.pi := by ring
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc (sixVertexEvenSymmetricLift m q) (hrho y) (hclose y hy')
    dsimp [wmin] at hwmin
    change rhoLower - eta / wmin ≤ _ at hx
    have heta' : eta / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      calc
        eta ≤ rhoLower * wmin / 2 := by simpa [wmin] using heta
        _ = rhoLower / 2 * wmin := by ring
    rw [hxy]
    linarith
  exact sixVertexEvenSymmetricBetheRootJacobian_injective_of_finiteDensityLower
    hc hm hN hcount hopen hsol (by linarith) hdensityHalf hmargin

theorem sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
    {a b : Real} (ha : 2 < a) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N) (hcount : m + m ≤ N)
    (rho : C(Set.Icc a b × Real, Real))
    {rhoLower outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ (t : Set.Icc a b) x,
      rhoLower ≤ sixVertexContinuumDensityAt rho t x)
    (houter : ∀ t : Set.Icc a b, outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude t.1 - 1) /
        sixVertexRootDensityScale t.1) / 2)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z : SixVertexBetheContinuationSpace a b N (m + m))
    (hgauge : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z < outer) :
    Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
  let t : Set.Icc a b := ⟨z.1.1, z.2.1⟩
  let q : Fin m → Real := sixVertexEvenPositiveHalfProjection m z.1.2
  have hc : 2 < z.1.1 := ha.trans_le z.2.1.1
  have hpopen : SixVertexOpenRootSimplex z.1.2 :=
    sixVertexBetheContinuationSet_subset_open ha hhalf z.2
  have hlift : sixVertexEvenSymmetricLift m q = z.1.2 :=
    sixVertexEvenSymmetricLift_projection m hpopen.2.1
  have hsol : SixVertexSatisfiesBetheEquations z.1.1 N (m + m) z.1.2 :=
    (sixVertexBetheUpdate_eq_self_iff hN z.1.2).mp z.2.2.2
  have hclose : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight z.1.1 x *
        (sixVertexFiniteRootDensity z.1.1 N (m + m)
          (sixVertexEvenSymmetricLift m q) x -
            sixVertexContinuumDensityAt rho t x)| ≤ outer := by
    intro x hx
    have hpoint := abs_weightedFiniteDensity_sub_le_gauge
      hc (N := N) z.1.2 (sixVertexContinuumDensitySection rho z) x hx
    have hle := hpoint.trans hgauge.le
    simpa only [hlift, sixVertexContinuumDensitySection, t] using hle
  have hopenLift : SixVertexOpenRootSimplex
      (sixVertexEvenSymmetricLift m q) := by
    rw [hlift]
    exact hpopen
  have hsolLift : SixVertexSatisfiesBetheEquations z.1.1 N (m + m)
      (sixVertexEvenSymmetricLift m q) := by
    rw [hlift]
    exact hsol
  change Function.Injective
    (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 q)
  exact sixVertexEvenSymmetricBetheRootJacobian_injective_of_weightedDensityClose
    hc hm hN hcount hopenLift hsolLift hrhoLower (hrho t) (houter t)
      hclose (hmargin t)

theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_densityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hhalf : N = 2 * (m + m))
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
          sixVertexFiniteDensityContinuumErrorOfLower
            t.1 N (rhoLower / 2) ≤ inner)
    (hmargin : ∀ t : Set.Icc a b,
      sixVertexSymmetricScatteringBoundaryBound t.1 +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower
          t.1 N (rhoLower / 2) < 2 * Real.pi)
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
  let k := m + m - 1
  have hk : k + 1 = m + m := by
    dsimp [k]
    omega
  have hrootCount : m + m ≤ N := by omega
  have hcover : 2 * (m + m) ≤ N := by omega
  let g : SixVertexBetheContinuationSpace a b N (m + m) → Real :=
    sixVertexContinuationWeightedFiniteDensityGauge ha N (m + m) rho
  have hg : Continuous g :=
    continuous_sixVertexContinuationWeightedFiniteDensityGauge
      ha N (m + m) rho
  have hgap : ∀ z, ¬(inner < g z ∧ g z < outer) := by
    intro z
    have hgap' :=
      sixVertexContinuationWeightedFiniteDensityGauge_solutionFreeAnnulus
        ha hN (n := k) (r := m + m) hk.symm (by omega) (by omega)
          rho hrhoEq hrhoMass
          hrhoLower hrho houter hinner
    simpa only [g] using hgap' z
  have hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)) := by
    intro z hzg
    exact sixVertexContinuationWeightedFiniteDensityGauge_jacobianInjective
      ha hm hN hcover hrootCount rho hrhoLower hrho houter hmargin z hzg
  exact exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge
    ha hab hc₀ hN hcover g hg hio hgap hjac z₀ hz₀g hz₀

end
end StatMech.FrontierD
