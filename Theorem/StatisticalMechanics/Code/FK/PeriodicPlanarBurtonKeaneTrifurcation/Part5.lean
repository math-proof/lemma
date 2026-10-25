/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


theorem PeriodicPlaneEmbedding.orbitTrifurcationHubs_card
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (u : V) (omega : ConfigSpace (Sym2 V)) (n : Nat) :
    (P.orbitTrifurcationHubs u omega n).card =
      (P.orbitTrifurcationCoords u omega n).card := by
  rw [PeriodicGraph.orbitTrifurcationHubs,
    Finset.card_image_of_injective]
  intro z w h
  have hv := congrArg (fun x => E.vertex x) h
  change E.vertex (P.shift z u) = E.vertex (P.shift w u) at hv
  rw [E.vertex_shift, E.vertex_shift] at hv
  exact E.period_injective (add_left_cancel hv)

theorem PeriodicPlaneEmbedding.orbitTrifurcation_count_le_shell
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (u : V) (hu : u ∈ P.fundamentalDomain)
    (omega : ConfigSpace (Sym2 V)) (n : Nat) :
    (P.orbitTrifurcationCoords u omega n).card <=
      (P.orbitShell n P.neighborOrbitRadius).card := by
  classical
  rw [← E.orbitTrifurcationHubs_card u omega n]
  apply finite_cutHub_count_of_ambient (P.openSubgraph omega)
    (P.orbitTrifurcationHubs u omega n)
    (P.orbitShell n P.neighborOrbitRadius)
  intro x hx
  rw [PeriodicGraph.orbitTrifurcationHubs, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [PeriodicGraph.orbitTrifurcationCoords, Finset.mem_filter] at hz
  have hxbox : P.shift z u ∈ P.orbitBox n := by
    rw [P.mem_orbitBox_iff]
    exact ⟨z, by simpa using hz.1, u, hu, rfl⟩
  exact P.trifurcation_orbitShell_witnesses omega n hxbox hz.2

theorem PeriodicGraph.orbitTrifurcationCoords_cast_eq_sum_indicator
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) :
    ((P.orbitTrifurcationCoords u omega n).card : ENNReal) =
      ∑ z ∈ (box_finite 2 n).toFinset,
        ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
          (fun _ => (1 : ENNReal))) omega := by
  classical
  unfold PeriodicGraph.orbitTrifurcationCoords
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : P.IsTrifurcation omega (P.shift z u) <;> simp [h]

theorem PeriodicGraph.expected_orbitTrifurcationCoords
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (u : V) (n : Nat) :
    ∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu =
      ((box_finite 2 n).toFinset.card) •
        mu {omega | P.IsTrifurcation omega u} := by
  classical
  calc
    ∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu =
        ∫⁻ omega, ∑ z ∈ (box_finite 2 n).toFinset,
          ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
            (fun _ => (1 : ENNReal))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact P.orbitTrifurcationCoords_cast_eq_sum_indicator u omega n
    _ = ∑ z ∈ (box_finite 2 n).toFinset,
        ∫⁻ omega, ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator
          (fun _ => (1 : ENNReal))) omega ∂mu := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro z _
      exact Measurable.indicator measurable_const
        (P.measurableSet_isTrifurcation (P.shift z u))
    _ = ∑ z ∈ (box_finite 2 n).toFinset,
        mu {omega | P.IsTrifurcation omega (P.shift z u)} := by
      apply Finset.sum_congr rfl
      intro z _
      rw [MeasureTheory.lintegral_indicator
        (P.measurableSet_isTrifurcation (P.shift z u))]
      simp
    _ = ∑ _z ∈ (box_finite 2 n).toFinset,
        mu {omega | P.IsTrifurcation omega u} := by
      apply Finset.sum_congr rfl
      intro z _
      exact P.trifurcation_measure_eq_orbit mu hTI z u
    _ = ((box_finite 2 n).toFinset.card) •
        mu {omega | P.IsTrifurcation omega u} := by
      simp

theorem PeriodicGraph.orbitShell_polynomial_ratio_tendsto_zero
    (P : PeriodicGraph V) (c : Nat) :
    Tendsto (fun n =>
      ((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card : Nat) : Real) /
        (((2 * n + 1) ^ 2 : Nat) : Real)) atTop (nhds 0) := by
  let C : Real := 16 * ((c : Real) + 1) * P.fundamentalDomain.card
  have hupper : Tendsto (fun n : Nat => C / ((n : Real) + 1))
      atTop (nhds 0) := by
    have hden : Tendsto (fun n : Nat => (n : Real) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := C)).div_atTop hden
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hupper
  filter_upwards [eventually_ge_atTop c] with n hn
  have hsub : (2 * n + 1) ^ 2 <= (2 * (n + c) + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hcastSub :
      ((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2 : Nat) : Real)) =
        ((2 * ((n : Real) + c) + 1) ^ 2 -
          (2 * (n : Real) + 1) ^ 2) := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  have hnreal : (c : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) <= n := by positivity
  have hc0 : (0 : Real) <= c := by positivity
  have hfd0 : (0 : Real) <= P.fundamentalDomain.card := by positivity
  have hcn : (c : Real) * n <= ((c : Real) + 1) * (n + 1) := by
    exact mul_le_mul (by linarith) (by linarith) hn0 (by linarith)
  have hcc : (c : Real) * c <= ((c : Real) + 1) * (n + 1) := by
    exact mul_le_mul (by linarith) (by linarith) hc0 (by linarith)
  have hdiff :
      (2 * ((n : Real) + c) + 1) ^ 2 - (2 * (n : Real) + 1) ^ 2 <=
        16 * ((c : Real) + 1) * (n + 1) := by
    nlinarith [hcn, hcc]
  have hnum :
      (((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) *
        P.fundamentalDomain.card : Nat) : Real)) <=
        C * ((n : Real) + 1) := by
    rw [Nat.cast_mul, hcastSub]
    dsimp [C]
    calc
      ((2 * ((n : Real) + c) + 1) ^ 2 - (2 * (n : Real) + 1) ^ 2) *
          P.fundamentalDomain.card <=
          (16 * ((c : Real) + 1) * (n + 1)) *
            P.fundamentalDomain.card :=
        mul_le_mul_of_nonneg_right hdiff hfd0
      _ = 16 * ((c : Real) + 1) * P.fundamentalDomain.card * (n + 1) := by
        ring
  have hden : ((n : Real) + 1) ^ 2 <=
      (((2 * n + 1) ^ 2 : Nat) : Real) := by
    push_cast
    nlinarith
  have hn1 : (0 : Real) < n + 1 := by positivity
  have hD : (0 : Real) < (((2 * n + 1) ^ 2 : Nat) : Real) := by positivity
  rw [div_le_div_iff₀ hD hn1]
  have hC0 : 0 <= C := by dsimp [C]; positivity
  nlinarith


theorem PeriodicPlaneEmbedding.trifurcation_measure_eq_zero
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (u : V)
    (hu : u ∈ P.fundamentalDomain) :
    mu {omega | P.IsTrifurcation omega u} = 0 := by
  let pr : Real := mu.real {omega | P.IsTrifurcation omega u}
  have hratio := P.orbitShell_polynomial_ratio_tendsto_zero P.neighborOrbitRadius
  have hle : ∀ n : Nat, pr <=
      ((((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
          (2 * n + 1) ^ 2) * P.fundamentalDomain.card : Nat) : Real) /
        (((2 * n + 1) ^ 2 : Nat) : Real) := by
    intro n
    have hexp := P.expected_orbitTrifurcationCoords mu hTI u n
    have hlin : ∫⁻ omega,
        ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu <=
        ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := by
      calc
        (∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu) <=
            ∫⁻ _omega : ConfigSpace (Sym2 V),
              ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((P.orbitTrifurcationCoords u omega n).card : ENNReal) <=
            ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal)
          exact_mod_cast E.orbitTrifurcation_count_le_shell u hu omega n
        _ = ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := by simp
    rw [hexp] at hlin
    have hpoly := P.orbitShell_card_le n P.neighborOrbitRadius
    have hENN : (((box_finite 2 n).toFinset.card : Nat) : ENNReal) *
        mu {omega | P.IsTrifurcation omega u} <=
      (((((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
        (2 * n + 1) ^ 2) * P.fundamentalDomain.card : Nat)) : ENNReal) := by
      calc
        (((box_finite 2 n).toFinset.card : Nat) : ENNReal) *
            mu {omega | P.IsTrifurcation omega u} =
            ((box_finite 2 n).toFinset.card) •
              mu {omega | P.IsTrifurcation omega u} := by simp [nsmul_eq_mul]
        _ <= ((P.orbitShell n P.neighborOrbitRadius).card : ENNReal) := hlin
        _ <= _ := by exact_mod_cast hpoly
    have hboxcard : (box_finite 2 n).toFinset.card = (2 * n + 1) ^ 2 := by
      rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
    let B : Nat := ((2 * (n + P.neighborOrbitRadius) + 1) ^ 2 -
      (2 * n + 1) ^ 2) * P.fundamentalDomain.card
    have hENN' : ((((2 * n + 1) ^ 2 : Nat) : ENNReal)) *
        mu {omega | P.IsTrifurcation omega u} <= (B : ENNReal) := by
      simpa only [hboxcard, B] using hENN
    have hright_ne_top : (B : ENNReal) ≠ (⊤ : ENNReal) := by simp
    have hreal0 := ENNReal.toReal_mono hright_ne_top hENN'
    have hreal : ((((2 * n + 1) ^ 2 : Nat) : Real) * pr <= (B : Real)) := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal0
    have hden : (0 : Real) < (((2 * n + 1) ^ 2 : Nat) : Real) := by positivity
    change pr <= (B : Real) / (((2 * n + 1) ^ 2 : Nat) : Real)
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hreal
  have hpr0 : pr <= 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hratio hle
  have hpreal : pr = 0 := le_antisymm hpr0 measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top mu _)).1 hpreal

end StatMech.FK.PeriodicPlanar
