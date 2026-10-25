/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Def.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part3
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem pairConfig_preimage_multiOpen [DecidableEq E]
    (T : Finset (E ⊕ E)) :
    Function.uncurry pairConfig ⁻¹' fmu_multiOpen T =
      fmu_multiOpen (pairLeft T) ×ˢ fmu_multiOpen (pairRight T) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, fmu_multiOpen, Set.mem_setOf_eq]
  constructor
  · intro h
    constructor
    · intro e he
      simp only [pairLeft, Finset.mem_biUnion] at he
      obtain ⟨z, hzT, hz⟩ := he
      cases z with
      | inl a =>
          have hea : e = a := by simpa using hz
          subst e
          simpa [Function.uncurry, pairConfig] using h (Sum.inl a) hzT
      | inr a => simp at hz
    · intro e he
      simp only [pairRight, Finset.mem_biUnion] at he
      obtain ⟨z, hzT, hz⟩ := he
      cases z with
      | inl a => simp at hz
      | inr a =>
          have hea : e = a := by simpa using hz
          subst e
          simpa [Function.uncurry, pairConfig] using h (Sum.inr a) hzT
  · rintro ⟨hleft, hright⟩ z hzT
    cases z with
    | inl e =>
        exact hleft e (by simp [pairLeft, hzT])
    | inr e =>
        exact hright e (by simp [pairRight, hzT])

theorem independentPairConfigLaw_real_multiOpen [DecidableEq E]
    (rho : ProbabilityMeasure (ConfigSpace E)) (T : Finset (E ⊕ E)) :
    (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T) =
      (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
        (rho : Measure _).real (fmu_multiOpen (pairRight T)) := by
  have hleft : (((independentPairConfigLaw rho) (fmu_multiOpen T) : NNReal) : Real) =
      (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable
    (fmu_multiOpen_measurable T)]
  rw [pairConfig_preimage_multiOpen]
  rw [← measureReal_prod_prod]
  rfl

theorem pairConfig_preimage_multiOpen_inter_shift [DecidableEq E]
    (g : H) (T U : Finset (E ⊕ E)) :
    Function.uncurry pairConfig ⁻¹'
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) =
      (fmu_multiOpen (pairLeft T) ∩
          (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) ×ˢ
        (fmu_multiOpen (pairRight T) ∩
          (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod]
  have hT := Set.ext_iff.mp (pairConfig_preimage_multiOpen T) p
  have hU := Set.ext_iff.mp (pairConfig_preimage_multiOpen U)
    (shift g p.1, shift g p.2)
  constructor
  · rintro ⟨hpT, hpU⟩
    have hpT' : p.1 ∈ fmu_multiOpen (pairLeft T) ∧
        p.2 ∈ fmu_multiOpen (pairRight T) := hT.mp hpT
    have hpU0 : pairConfig (shift g p.1) (shift g p.2) ∈
        fmu_multiOpen U := by rwa [pairConfig_shift]
    have hpU' : shift g p.1 ∈ fmu_multiOpen (pairLeft U) ∧
        shift g p.2 ∈ fmu_multiOpen (pairRight U) := hU.mp hpU0
    exact ⟨⟨hpT'.1, hpU'.1⟩, hpT'.2, hpU'.2⟩
  · rintro ⟨⟨hpTL, hpUL⟩, hpTR, hpUR⟩
    have hpT : pairConfig p.1 p.2 ∈ fmu_multiOpen T :=
      hT.mpr ⟨hpTL, hpTR⟩
    have hpU0 : pairConfig (shift g p.1) (shift g p.2) ∈
        fmu_multiOpen U := hU.mpr ⟨hpUL, hpUR⟩
    have hpU : shift g (pairConfig p.1 p.2) ∈ fmu_multiOpen U := by
      simpa only [pairConfig_shift] using hpU0
    exact ⟨hpT, hpU⟩

theorem independentPairConfigLaw_real_inter_shift [DecidableEq E]
    (rho : ProbabilityMeasure (ConfigSpace E)) (g : H)
    (T U : Finset (E ⊕ E)) :
    (independentPairConfigLaw rho : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) =
      (rho : Measure _).real
          (fmu_multiOpen (pairLeft T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) *
        (rho : Measure _).real
          (fmu_multiOpen (pairRight T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
  have hset : MeasurableSet
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) :=
    (fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable U).preimage (measurable_shift g))
  have hleft : (((independentPairConfigLaw rho)
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) : NNReal) : Real) =
      (independentPairConfigLaw rho : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable hset]
  rw [pairConfig_preimage_multiOpen_inter_shift]
  rw [← measureReal_prod_prod]
  rfl


theorem independentPairConfigLaw_pairMixing
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    fmu_PairMixing (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  classical
  intro P epsilon hepsilon
  let Q : Finset (Finset E) :=
    P.image pairLeft ∪ P.image pairRight
  let delta := epsilon / 3
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨g, hg⟩ := hmix (Q.image fmu_multiOpen)
    (by
      intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨T, hT, rfl⟩ := hA
      exact fmu_multiOpen_mem_measurableCylinders T)
    delta hdelta
  refine ⟨g, ?_⟩
  intro T hT U hU
  have hTL : pairLeft T ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hTR : pairRight T ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hUL : pairLeft U ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hUR : pairRight U ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hleft := hg (fmu_multiOpen (pairLeft T))
    (Finset.mem_image.mpr ⟨pairLeft T, hTL, rfl⟩)
    (fmu_multiOpen (pairLeft U))
    (Finset.mem_image.mpr ⟨pairLeft U, hUL, rfl⟩)
  have hright := hg (fmu_multiOpen (pairRight T))
    (Finset.mem_image.mpr ⟨pairRight T, hTR, rfl⟩)
    (fmu_multiOpen (pairRight U))
    (Finset.mem_image.mpr ⟨pairRight U, hUR, rfl⟩)
  let a := (rho : Measure _).real
    (fmu_multiOpen (pairLeft T) ∩
      (shift g) ⁻¹' fmu_multiOpen (pairLeft U))
  let b := (rho : Measure _).real
    (fmu_multiOpen (pairRight T) ∩
      (shift g) ⁻¹' fmu_multiOpen (pairRight U))
  let c := (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
    (rho : Measure _).real (fmu_multiOpen (pairLeft U))
  let e := (rho : Measure _).real (fmu_multiOpen (pairRight T)) *
    (rho : Measure _).real (fmu_multiOpen (pairRight U))
  have ha : 0 ≤ a := measureReal_nonneg
  have hb : 0 ≤ b := measureReal_nonneg
  have hc : 0 ≤ c := mul_nonneg measureReal_nonneg measureReal_nonneg
  have he : 0 ≤ e := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hb1 : b ≤ 1 := measureReal_le_one
  have hc1 : c ≤ 1 :=
    mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  change abs (_ - _) < epsilon
  rw [independentPairConfigLaw_real_inter_shift,
    independentPairConfigLaw_real_multiOpen,
    independentPairConfigLaw_real_multiOpen]
  change abs (a * b -
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight U)))) < epsilon
  rw [show
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight U))) = c * e by
      dsimp [c, e]
      ring]
  have hab : a * b - c * e = (a - c) * b + c * (b - e) := by ring
  rw [hab]
  calc
    abs ((a - c) * b + c * (b - e)) ≤
        abs (a - c) * abs b + abs c * abs (b - e) := by
      simpa [abs_mul] using abs_add_le ((a - c) * b) (c * (b - e))
    _ < delta * 1 + 1 * delta := by
      have habsB : abs b ≤ 1 := by rw [abs_of_nonneg hb]; exact hb1
      have habsC : abs c ≤ 1 := by rw [abs_of_nonneg hc]; exact hc1
      exact add_lt_add_of_lt_of_lt
        (mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
          hleft habsB (abs_nonneg _) zero_lt_one)
        (mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          habsC hright (abs_nonneg _) zero_lt_one)
    _ < epsilon := by dsimp [delta]; linarith


theorem pairConfig_measurePreserving
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving (Function.uncurry pairConfig)
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E))
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  change MeasurePreserving (Function.uncurry pairConfig) _
    (Measure.map (Function.uncurry pairConfig)
      ((rho : Measure (ConfigSpace E)).prod (rho : Measure (ConfigSpace E))))
  exact measurable_pairConfig.measurePreserving _

theorem independentPairConfigLaw_isTranslationInvariant
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E))) :
    IsTranslationInvariant (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  intro g
  have hprod : MeasurePreserving
      (Prod.map (shift g) (shift g))
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E))
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E)) :=
    (hti g).prod (hti g)
  have hsemiconj : Function.Semiconj (Function.uncurry pairConfig)
      (Prod.map (shift g : ConfigSpace E -> ConfigSpace E)
        (shift g : ConfigSpace E -> ConfigSpace E))
      (shift g : ConfigSpace (E ⊕ E) -> ConfigSpace (E ⊕ E)) := by
    intro p
    exact pairConfig_shift g p.1 p.2
  exact (pairConfig_measurePreserving rho).of_semiconj hprod hsemiconj
    (measurable_shift g)


theorem independentPairConfigLaw_isErgodic
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    IsErgodic (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) :=
  fmu_isErgodic_of_pairMixing
    (independentPairConfigLaw_isTranslationInvariant rho hti)
    (independentPairConfigLaw_pairMixing rho hmix)


end StatMech.FrontierB
