/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Def.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem currentTrace_preimage_cylinder (S : Finset E)
    (A : Set (↑S -> Bool)) :
    currentTrace ⁻¹' MeasureTheory.cylinder S A =
      currentCylinder S (tracePullbackPatternSet S A) := by
  rfl

theorem currentTrace_preimage_mem_measurableCylinders
    {C : Set (ConfigSpace E)}
    (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
    currentTrace ⁻¹' C ∈ measurableCylinders (fun _ : E => Nat) := by
  rw [mem_measurableCylinders] at hC ⊢
  obtain ⟨S, A, hA, rfl⟩ := hC
  exact ⟨S, tracePullbackPatternSet S A, MeasurableSet.of_discrete,
    currentTrace_preimage_cylinder S A⟩

theorem currentTraceLaw_real (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A) :
    (currentTraceLaw mu : Measure (ConfigSpace E)).real A =
      (mu : Measure (InfiniteCurrentConfig E)).real (currentTrace ⁻¹' A) := by
  have hleft : (((currentTraceLaw mu) A : NNReal) : Real) =
      (currentTraceLaw mu : Measure (ConfigSpace E)).real A := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  have hright : ((mu (currentTrace ⁻¹' A) : NNReal) : Real) =
      (mu : Measure (InfiniteCurrentConfig E)).real (currentTrace ⁻¹' A) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft, ← hright]
  exact congrArg (fun z : NNReal => (z : Real))
    (ProbabilityMeasure.map_apply mu
      continuous_currentTrace.measurable.aemeasurable hA)

theorem currentTrace_preimage_inter_shift (g : H)
    (A B : Set (ConfigSpace E)) :
    currentTrace ⁻¹' (A ∩ (shift g) ⁻¹' B) =
      (currentTrace ⁻¹' A) ∩ (currentShift g) ⁻¹' (currentTrace ⁻¹' B) := by
  ext m
  rfl


theorem currentTraceLaw_genMixing
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (hmix : CurrentCylinderPairMixing (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    fmu_GenMixing (G := H) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  intro family hfamily epsilon hepsilon
  let pulled : Finset (Set (InfiniteCurrentConfig E)) :=
    family.image (fun A => currentTrace ⁻¹' A)
  have hpulled : ∀ A ∈ pulled,
      A ∈ measurableCylinders (fun _ : E => Nat) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact currentTrace_preimage_mem_measurableCylinders (hfamily C hC)
  obtain ⟨g, hg⟩ := hmix pulled hpulled epsilon hepsilon
  refine ⟨g, ?_⟩
  intro A hA B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  have hABmeas : MeasurableSet (A ∩ (shift g) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage (measurable_shift g))
  have hPA : currentTrace ⁻¹' A ∈ pulled :=
    Finset.mem_image.mpr ⟨A, hA, rfl⟩
  have hPB : currentTrace ⁻¹' B ∈ pulled :=
    Finset.mem_image.mpr ⟨B, hB, rfl⟩
  have hcore := hg (currentTrace ⁻¹' A) hPA (currentTrace ⁻¹' B) hPB
  rw [currentTraceLaw_real mu hABmeas,
    currentTraceLaw_real mu hAmeas, currentTraceLaw_real mu hBmeas,
    currentTrace_preimage_inter_shift] 
  exact hcore


theorem infinitePlusCurrentTraceLaw_genMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_GenMixing (G := Multiplicative (Lattice.Site d))
      (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :=
  currentTraceLaw_genMixing _
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)


end StatMech.FrontierB
