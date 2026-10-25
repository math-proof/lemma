/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part2


namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

@[simp] theorem sixVertexCanonicalOddHalfPartitionRoot_eq
    {c : Real} (hc : 2 < c) (s k j : Nat) (hj : j < s + k + 2) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k j =
      sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
        ⟨j, by omega⟩ := by
  simp [sixVertexCanonicalOddHalfPartitionRoot, hj]

theorem sixVertexCanonicalOddHalfPartitionRoot_left
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k j.val =
      sixVertexCanonicalOddLeftHalfRoot hc s k j := by
  unfold sixVertexCanonicalOddLeftHalfRoot
  rw [sixVertexCanonicalOddHalfPartitionRoot_eq hc s k j.val (by omega)]

theorem sixVertexCanonicalOddHalfPartitionRoot_right
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k (j.val + 1) =
      sixVertexCanonicalOddRightHalfRoot hc s k j := by
  unfold sixVertexCanonicalOddRightHalfRoot
  rw [sixVertexCanonicalOddHalfPartitionRoot_eq hc s k (j.val + 1)
    (by omega)]

theorem sixVertexCanonicalOddHalfPartitionRoot_last
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalOddHalfPartitionRoot hc s k (s + k + 1) =
      sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
  simp [sixVertexCanonicalOddBoundaryHalfRoot]

theorem sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
    sixVertexCanonicalOddLeftHalfRoot hc s k
        (0 : Fin (s + k + 1)) <=
      1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let rho := sixVertexFiniteRootDensity c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k
    (0 : Fin (s + k + 1))
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have ha : 0 < a := by
    dsimp [a, sixVertexCanonicalOddLeftHalfRoot]
    exact (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))).1
  have hpSymm : SixVertexRootSymmetric p :=
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.1
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p 0 a
  have hzero := sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  have hroot := sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k
    (0 : Fin (s + k + 1))
  have hmass : (∫ x in (0 : Real)..a, rho x) = 1 / (2 * (N : Real)) := by
    rw [show (∫ x in (0 : Real)..a, rho x) =
        sixVertexBetheCountingFunction c N n p a -
          sixVertexBetheCountingFunction c N n p 0 by
      simpa [rho] using hint]
    rw [hzero]
    have hroot' : sixVertexBetheCountingFunction c N n p a =
        (1 / 2 : Real) / N := by simpa [N, n, p, a] using hroot
    rw [hroot']
    field_simp [hNreal.ne']
    ring
  have hmono := intervalIntegral.integral_mono_on ha.le
    (continuous_const.intervalIntegrable (μ := volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _)
    (fun x _ => by simpa [rho, N, n, p] using hdensity x)
  rw [intervalIntegral.integral_const, hmass] at hmono
  simp only [smul_eq_mul, sub_zero] at hmono
  dsimp [a, N] at hmono ⊢
  rw [show 1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower) =
      (1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real))) / lower by
    ring]
  exact (le_div_iff₀ hlower).2 hmono

theorem tendsto_sixVertexCanonicalOddFirstLeftHalfRoot
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => sixVertexCanonicalOddLeftHalfRoot hc s k
      (0 : Fin (s + k + 1))) atTop (nhds 0) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hden : Tendsto (fun k =>
      (2 * lower) * (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := hwidth.const_mul_atTop (mul_pos (by norm_num) hlower)
  have hmajor : Tendsto (fun k =>
      1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (tendsto_const_nhds.div_atTop hden :
        Tendsto (fun k => (1 : Real) /
          ((2 * lower) * (sixVertexFourWidth (2 * s + 1) k : Real)))
          atTop (nhds 0))
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards [hfloor] with k hk
  have hk' : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, sixVertexFourWidth] using hk
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos]
  · exact sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower
      hc s k hlower hk'
  · dsimp [sixVertexCanonicalOddLeftHalfRoot]
    exact (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))).1

theorem tendsto_sixVertexCanonicalOddFixedHalfIncrementError
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      2 * ∑ j : Fin (s + k + 1),
        (sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
      (sixVertexBetheDesingularizedLogObservable c
          (sixVertexCanonicalOddBoundaryHalfRoot hc s k
            (0 : Fin (s + 1))) -
        sixVertexBetheDesingularizedLogObservable c
          (sixVertexCanonicalOddLeftHalfRoot hc s k
            (0 : Fin (s + k + 1))))) atTop (nhds 0) := by
  let H := sixVertexBetheDesingularizedLogObservable c
  let D := sixVertexBetheDesingularizedLogObservableDerivative c
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hH : ContinuousOn H (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservable hc
  have hD : ContinuousOn D (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservableDerivative hc
  have hderiv : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt H (D x) x := by
    intro x hx
    exact hasDerivAt_sixVertexBetheDesingularizedLogObservable hc hx
  have huniform : UniformContinuousOn D (Set.Icc 0 Real.pi) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hD
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hden := hwidth.atTop_mul_const hlower
  have hmesh : Tendsto (fun k =>
      1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let E := epsilon / (Real.pi + 1)
  have hE : 0 < E := by dsimp [E]; positivity
  rcases Metric.uniformContinuousOn_iff.mp huniform E hE with
    ⟨delta, hdelta, hmod⟩
  have hmeshEventually : ∀ᶠ k : Nat in atTop,
      1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) < delta := by
    have hball := (Metric.tendsto_nhds.mp hmesh) delta hdelta
    filter_upwards [hball] with k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity)] at hk
    exact hk
  filter_upwards [hfloor, hmeshEventually] with k hkFloor hkMesh
  let n := s + k + 1
  let a : Nat -> Real := sixVertexCanonicalOddHalfPartitionRoot hc s k
  have hkDensity : ∀ x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, sixVertexFourWidth] using hkFloor
  have ha (j : Nat) (hj : j <= n) : a j ∈ Set.Icc 0 Real.pi := by
    have hjlt : j < s + k + 2 := by dsimp [n] at hj; omega
    rw [show a j =
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc
          (2 * s + 1 + k) ⟨j, by omega⟩ by
      exact sixVertexCanonicalOddHalfPartitionRoot_eq hc s k j hjlt]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j, by omega⟩
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hordered (j : Nat) (hj : j < n) : a j <= a (j + 1) := by
    let jf : Fin (s + k + 1) := ⟨j, by simpa [n] using hj⟩
    rw [show a j = sixVertexCanonicalOddLeftHalfRoot hc s k
        jf by
          dsimp [a, jf]
          exact sixVertexCanonicalOddHalfPartitionRoot_left hc s k jf]
    rw [show a (j + 1) = sixVertexCanonicalOddRightHalfRoot hc s k
        jf by
          dsimp [a, jf]
          exact sixVertexCanonicalOddHalfPartitionRoot_right hc s k jf]
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hclose (j : Nat) (hj : j < n) (x : Real)
      (hx : x ∈ Set.Icc (a j) (a (j + 1))) :
      |D x - D ((a j + a (j + 1)) / 2)| <= E := by
    let jf : Fin (s + k + 1) := ⟨j, by simpa [n] using hj⟩
    have hgap := sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower
      hc s k hlower hkDensity jf
    have haj : a j = sixVertexCanonicalOddLeftHalfRoot hc s k jf := by
      dsimp [a]
      exact sixVertexCanonicalOddHalfPartitionRoot_left hc s k jf
    have haj1 : a (j + 1) = sixVertexCanonicalOddRightHalfRoot hc s k jf := by
      dsimp [a]
      exact sixVertexCanonicalOddHalfPartitionRoot_right hc s k jf
    have hxGlobal : x ∈ Set.Icc 0 Real.pi :=
      ⟨(ha j hj.le).1.trans hx.1, hx.2.trans (ha (j + 1) (by omega)).2⟩
    have hmidGlobal : (a j + a (j + 1)) / 2 ∈ Set.Icc 0 Real.pi := by
      have hjmem := ha j hj.le
      have hj1mem := ha (j + 1) (by omega)
      constructor <;> nlinarith [hjmem.1, hjmem.2, hj1mem.1, hj1mem.2]
    have hdist : dist x ((a j + a (j + 1)) / 2) < delta := by
      rw [Real.dist_eq]
      have hinside : |x - (a j + a (j + 1)) / 2| <= a (j + 1) - a j := by
        rw [abs_le]
        constructor <;> nlinarith [hx.1, hx.2]
      calc
        _ <= a (j + 1) - a j := hinside
        _ <= 1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
          simpa [haj, haj1] using hgap
        _ < delta := hkMesh
    have := hmod x hxGlobal ((a j + a (j + 1)) / 2) hmidGlobal hdist
    simpa [Real.dist_eq] using this.le
  have hbound := abs_two_halfIncrementSum_sub_endpoint_le a ha hordered
    hH hD hderiv hE.le hclose
  have hlen : a n - a 0 <= Real.pi := by
    linarith [(ha n le_rfl).2, (ha 0 (by omega)).1]
  have hbound' :
      |2 * ∑ j : Fin (s + k + 1),
          (H (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
            H (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
        (H (sixVertexCanonicalOddBoundaryHalfRoot hc s k
            (0 : Fin (s + 1))) -
          H (sixVertexCanonicalOddLeftHalfRoot hc s k
            (0 : Fin (s + k + 1))))| <= E * (a n - a 0) := by
    simpa [n, a, sixVertexCanonicalOddMidpointHalfRoot,
      sixVertexCanonicalOddHalfPartitionRoot_left,
      sixVertexCanonicalOddHalfPartitionRoot_right,
      sixVertexCanonicalOddHalfPartitionRoot_last] using hbound
  rw [Real.dist_eq, sub_zero]
  change |2 * ∑ j : Fin (s + k + 1),
      (H (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
        H (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
      (H (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))) -
        H (sixVertexCanonicalOddLeftHalfRoot hc s k
          (0 : Fin (s + k + 1))))| < epsilon
  calc
    _ <= E * (a n - a 0) := hbound'
    _ <= E * Real.pi := mul_le_mul_of_nonneg_left hlen hE.le
    _ < epsilon := by
      dsimp [E]
      have hpi : 0 < Real.pi := Real.pi_pos
      calc
        epsilon / (Real.pi + 1) * Real.pi <
            epsilon / (Real.pi + 1) * (Real.pi + 1) := by
          exact mul_lt_mul_of_pos_left (by linarith)
            (div_pos hepsilon (by positivity))
        _ = epsilon := by field_simp

theorem tendsto_sixVertexCanonicalOddFixedHalfIncrement
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      2 * ∑ j : Fin (s + k + 1),
        (sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheDesingularizedLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j))) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
        Real.log Real.pi - Real.log (c ^ 2))) := by
  let H := sixVertexBetheDesingularizedLogObservable c
  have hH : ContinuousOn H (Set.Icc 0 Real.pi) :=
    continuousOn_sixVertexBetheDesingularizedLogObservable hc
  let boundary : Nat -> Real := fun k =>
    sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))
  let first : Nat -> Real := fun k =>
    sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))
  have hboundaryRoot : Tendsto boundary atTop (nhds Real.pi) := by
    exact tendsto_sixVertexCanonicalOddBoundaryHalfRoot hc s
      (0 : Fin (s + 1))
  have hboundaryMem : ∀ᶠ k : Nat in atTop,
      boundary k ∈ Set.Icc 0 Real.pi := by
    apply Eventually.of_forall
    intro k
    dsimp [boundary, sixVertexCanonicalOddBoundaryHalfRoot]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨s + k + 1, by omega⟩
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hboundaryWithin : Tendsto boundary atTop
      (nhdsWithin Real.pi (Set.Icc 0 Real.pi)) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.mpr
      ⟨hboundaryRoot, Filter.tendsto_principal.mpr hboundaryMem⟩
  have hboundaryH : Tendsto (fun k => H (boundary k)) atTop
      (nhds (H Real.pi)) := by
    have hHpi : Tendsto H (nhdsWithin Real.pi (Set.Icc 0 Real.pi))
        (nhds (H Real.pi)) := hH Real.pi ⟨Real.pi_pos.le, le_rfl⟩
    exact hHpi.comp hboundaryWithin
  have hfirstRoot : Tendsto first atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalOddFirstLeftHalfRoot hc s
  have hfirstMem : ∀ᶠ k : Nat in atTop,
      first k ∈ Set.Icc 0 Real.pi := by
    apply Eventually.of_forall
    intro k
    dsimp [first, sixVertexCanonicalOddLeftHalfRoot]
    have hmem := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) (0 : Fin (2 * s + 1 + k + 1))
    exact ⟨hmem.1.le, hmem.2.le⟩
  have hfirstWithin : Tendsto first atTop
      (nhdsWithin 0 (Set.Icc 0 Real.pi)) := by
    rw [nhdsWithin]
    exact Filter.tendsto_inf.mpr
      ⟨hfirstRoot, Filter.tendsto_principal.mpr hfirstMem⟩
  have hfirstH : Tendsto (fun k => H (first k)) atTop (nhds (H 0)) := by
    have hHzero : Tendsto H (nhdsWithin 0 (Set.Icc 0 Real.pi))
        (nhds (H 0)) := hH 0 ⟨le_rfl, Real.pi_pos.le⟩
    exact hHzero.comp hfirstWithin
  have herror := tendsto_sixVertexCanonicalOddFixedHalfIncrementError hc s
  have hcomb := herror.add (hboundaryH.sub hfirstH)
  have hpi := sixVertexBetheDesingularizedLogObservable_pi hc
  have hzero := sixVertexBetheDesingularizedLogObservable_zero hc
  convert hcomb using 1
  · funext k
    dsimp [boundary, first, H]
    ring
  · dsimp [H] at hpi hzero ⊢
    rw [hpi, hzero]
    ring

end
end StatMech.FrontierD
