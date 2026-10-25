/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
import Def.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem independentMixedPairConfigLaw_real_multiOpen [DecidableEq E]
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (T : Finset (E ⊕ E)) :
    (independentMixedPairConfigLaw rho nu : Measure _).real
        (fmu_multiOpen T) =
      (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
        (nu : Measure _).real (fmu_multiOpen (pairRight T)) := by
  have hleft : (((independentMixedPairConfigLaw rho nu)
      (fmu_multiOpen T) : NNReal) : Real) =
      (independentMixedPairConfigLaw rho nu : Measure _).real
        (fmu_multiOpen T) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentMixedPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable
    (fmu_multiOpen_measurable T)]
  rw [pairConfig_preimage_multiOpen]
  rw [← measureReal_prod_prod]
  rfl

theorem independentMixedPairConfigLaw_real_inter_shift [DecidableEq E]
    (rho nu : ProbabilityMeasure (ConfigSpace E)) (g : H)
    (T U : Finset (E ⊕ E)) :
    (independentMixedPairConfigLaw rho nu : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) =
      (rho : Measure _).real
          (fmu_multiOpen (pairLeft T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) *
        (nu : Measure _).real
          (fmu_multiOpen (pairRight T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
  have hset : MeasurableSet
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) :=
    (fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable U).preimage (measurable_shift g))
  have hleft : (((independentMixedPairConfigLaw rho nu)
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) : NNReal) :
        Real) =
      (independentMixedPairConfigLaw rho nu : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentMixedPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable hset]
  rw [pairConfig_preimage_multiOpen_inter_shift]
  rw [← measureReal_prod_prod]
  rfl

theorem mixedPairConfig_measurePreserving
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving (Function.uncurry pairConfig)
      (rho.prod nu : Measure (ConfigSpace E × ConfigSpace E))
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))) := by
  change MeasurePreserving (Function.uncurry pairConfig) _
    (Measure.map (Function.uncurry pairConfig)
      ((rho : Measure (ConfigSpace E)).prod
        (nu : Measure (ConfigSpace E))))
  exact measurable_pairConfig.measurePreserving _

theorem independentMixedPairConfigLaw_isTranslationInvariant
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hrho : IsTranslationInvariant (G := H)
      (rho : Measure (ConfigSpace E)))
    (hnu : IsTranslationInvariant (G := H)
      (nu : Measure (ConfigSpace E))) :
    IsTranslationInvariant (G := H)
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))) := by
  intro g
  have hprod : MeasurePreserving
      (Prod.map (shift g) (shift g))
      (rho.prod nu : Measure (ConfigSpace E × ConfigSpace E))
      (rho.prod nu : Measure (ConfigSpace E × ConfigSpace E)) :=
    (hrho g).prod (hnu g)
  have hsemiconj : Function.Semiconj (Function.uncurry pairConfig)
      (Prod.map (shift g : ConfigSpace E -> ConfigSpace E)
        (shift g : ConfigSpace E -> ConfigSpace E))
      (shift g : ConfigSpace (E ⊕ E) -> ConfigSpace (E ⊕ E)) := by
    intro p
    exact pairConfig_shift g p.1 p.2
  exact (mixedPairConfig_measurePreserving rho nu).of_semiconj
    hprod hsemiconj (measurable_shift g)


theorem independentMixedPairConfigLaw_pairMixing_of_axis
    (axis : Nat -> H)
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hrho : fmu_AxisCofinalGenMixing axis
      (rho : Measure (ConfigSpace E)))
    (hnu : fmu_AxisEventuallyGenMixing axis
      (nu : Measure (ConfigSpace E))) :
    fmu_PairMixing (G := H)
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))) := by
  classical
  intro P epsilon hepsilon
  let Q : Finset (Finset E) :=
    P.image pairLeft ∪ P.image pairRight
  let family : Finset (Set (ConfigSpace E)) := Q.image fmu_multiOpen
  have hfamily : ∀ A ∈ family,
      A ∈ measurableCylinders (fun _ : E => Bool) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨T, hT, rfl⟩ := hA
    exact fmu_multiOpen_mem_measurableCylinders T
  let delta := epsilon / 3
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hnuEventually := hnu family hfamily delta hdelta
  obtain ⟨K, hK⟩ := eventually_atTop.mp hnuEventually
  obtain ⟨k, hk, hrhoMix⟩ :=
    hrho family hfamily delta hdelta K
  have hnuMix := hK k hk
  refine ⟨axis k, ?_⟩
  intro T hT U hU
  have hTL : pairLeft T ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hTR : pairRight T ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hUL : pairLeft U ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hUR : pairRight U ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hleft := hrhoMix (fmu_multiOpen (pairLeft T))
    (Finset.mem_image.mpr ⟨pairLeft T, hTL, rfl⟩)
    (fmu_multiOpen (pairLeft U))
    (Finset.mem_image.mpr ⟨pairLeft U, hUL, rfl⟩)
  have hright := hnuMix (fmu_multiOpen (pairRight T))
    (Finset.mem_image.mpr ⟨pairRight T, hTR, rfl⟩)
    (fmu_multiOpen (pairRight U))
    (Finset.mem_image.mpr ⟨pairRight U, hUR, rfl⟩)
  let a := (rho : Measure _).real
    (fmu_multiOpen (pairLeft T) ∩
      (shift (axis k)) ⁻¹' fmu_multiOpen (pairLeft U))
  let b := (nu : Measure _).real
    (fmu_multiOpen (pairRight T) ∩
      (shift (axis k)) ⁻¹' fmu_multiOpen (pairRight U))
  let c := (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
    (rho : Measure _).real (fmu_multiOpen (pairLeft U))
  let e := (nu : Measure _).real (fmu_multiOpen (pairRight T)) *
    (nu : Measure _).real (fmu_multiOpen (pairRight U))
  have hb : 0 <= b := measureReal_nonneg
  have hc : 0 <= c := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hb1 : b <= 1 := measureReal_le_one
  have hc1 : c <= 1 :=
    mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  change abs (_ - _) < epsilon
  rw [independentMixedPairConfigLaw_real_inter_shift,
    independentMixedPairConfigLaw_real_multiOpen,
    independentMixedPairConfigLaw_real_multiOpen]
  change abs (a * b -
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight U)))) < epsilon
  rw [show
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (nu : Measure _).real (fmu_multiOpen (pairRight U))) = c * e by
      dsimp [c, e]
      ring]
  have hab : a * b - c * e = (a - c) * b + c * (b - e) := by ring
  rw [hab]
  calc
    abs ((a - c) * b + c * (b - e)) <=
        abs (a - c) * abs b + abs c * abs (b - e) := by
      simpa [abs_mul] using abs_add_le ((a - c) * b) (c * (b - e))
    _ < delta * 1 + 1 * delta := by
      have habsB : abs b <= 1 := by
        rw [abs_of_nonneg hb]
        exact hb1
      have habsC : abs c <= 1 := by
        rw [abs_of_nonneg hc]
        exact hc1
      exact add_lt_add_of_lt_of_lt
        (mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
          hleft habsB (abs_nonneg _) zero_lt_one)
        (mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          habsC hright (abs_nonneg _) zero_lt_one)
    _ < epsilon := by dsimp [delta]; linarith


theorem freePlusCurrentTracePairLaw_pairMixing
    {d : Nat} (hd : 1 <= d) {beta : Real} (hbeta : 0 < beta) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (independentMixedPairConfigLaw
        (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le))
        (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) :
          Measure (ConfigSpace
            (Sym2 (Site d) ⊕ Sym2 (Site d)))) :=
  independentMixedPairConfigLaw_pairMixing_of_axis
    (fun k => FK.freeAxisTranslationPower hd k) _ _
    (infiniteFreeCurrentTraceLaw_axisCofinalGenMixing hd hbeta)
    (infinitePlusCurrentTraceLaw_axisEventuallyGenMixing hd hbeta)


theorem freePlusCurrentTracePairLaw_genMixing
    {d : Nat} (hd : 1 <= d) {beta : Real} (hbeta : 0 < beta) :
    fmu_GenMixing (G := Multiplicative (Site d))
      (independentMixedPairConfigLaw
        (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le))
        (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) :
          Measure (ConfigSpace
            (Sym2 (Site d) ⊕ Sym2 (Site d)))) := by
  exact StatMech.FK.fmu_genMixing_of_pairMixing
    (freePlusCurrentTracePairLaw_pairMixing hd hbeta)

end StatMech.FrontierB
