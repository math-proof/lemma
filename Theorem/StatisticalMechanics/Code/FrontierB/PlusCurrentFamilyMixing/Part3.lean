/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentSingletonMixing
import Def.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part2
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK


theorem currentCylinder_liftCurrentPatternSet {E : Type*}
    {S U : Finset E} (hSU : S ⊆ U) (A : Set (↑S -> Nat)) :
    currentCylinder U (liftCurrentPatternSet hSU A) = currentCylinder S A := by
  ext m
  change Finset.restrict₂ (π := fun _ : E => Nat) hSU
      (restrictCurrent U m) ∈ A ↔ restrictCurrent S m ∈ A
  rw [restrictCurrent_restrict₂ hSU]


theorem infinitePlusCurrentMeasure_cylinderPairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentCylinderPairMixing (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) := by
  classical
  let nu := infinitePlusCurrentMeasure d beta hbeta.le
  let mu := (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
  intro family hfamily epsilon hepsilon
  let members := family.attach
  let support : ↑family -> Finset (Sym2 (Site d)) := fun C =>
    MeasureTheory.measurableCylinders.finset (hfamily C.1 C.2)
  let rawAccepted : (C : ↑family) -> Set (↑(support C) -> Nat) := fun C =>
    MeasureTheory.measurableCylinders.set (hfamily C.1 C.2)
  let U : Finset (Sym2 (Site d)) := members.biUnion support
  have hsupport (C : ↑family) : support C ⊆ U := by
    intro e he
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_attach _ C, he⟩
  let liftedAccepted (C : ↑family) : Set (↑U -> Nat) :=
    liftCurrentPatternSet (hsupport C) (rawAccepted C)
  have hrepr (C : ↑family) : C.1 =
      currentCylinder (support C) (rawAccepted C) := by
    simpa only [currentCylinder, restrictCurrent, MeasureTheory.cylinder,
      Finset.restrict] using
      (MeasureTheory.measurableCylinders.eq_cylinder (hfamily C.1 C.2))
  have hreprU (C : ↑family) : C.1 =
      currentCylinder U (liftedAccepted C) := by
    calc
      C.1 = currentCylinder (support C) (rawAccepted C) := hrepr C
      _ = currentCylinder U (liftedAccepted C) :=
        (currentCylinder_liftCurrentPatternSet
          (hsupport C) (rawAccepted C)).symm
  let L := latticeEdgePart d U
  have hL : (↑L : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    exact latticeEdgePart_lattice d U
  let reducedAccepted (C : ↑family) : Set (↑L -> Nat) :=
    latticeReducedPatternSet d U (liftedAccepted C)
  let reducedFamily : Finset (Set (↑L -> Nat)) :=
    members.image reducedAccepted
  obtain ⟨g, hmix⟩ :=
    infinitePlusCurrentMeasure_latticeCylinder_family_pairMixing hd hbeta
      L hL reducedFamily epsilon hepsilon
  refine ⟨g, ?_⟩
  intro A hA B hB
  let a : ↑family := ⟨A, hA⟩
  let b : ↑family := ⟨B, hB⟩
  have haMember : a ∈ members := Finset.mem_attach _ a
  have hbMember : b ∈ members := Finset.mem_attach _ b
  have haReduced : reducedAccepted a ∈ reducedFamily :=
    Finset.mem_image.mpr ⟨a, haMember, rfl⟩
  have hbReduced : reducedAccepted b ∈ reducedFamily :=
    Finset.mem_image.mpr ⟨b, hbMember, rfl⟩
  let AR := currentCylinder L (reducedAccepted a)
  let BR := currentCylinder L (reducedAccepted b)
  have hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet ->
      mu {m | m e = 0} = 1 := by
    intro e he
    exact plusCurrentLimit_nonlattice_zero d beta hbeta.le e he
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
  have haeAU := currentCylinder_ae_eq_latticeReduction d nu U hzero
    (liftedAccepted a)
  have haeBU := currentCylinder_ae_eq_latticeReduction d nu U hzero
    (liftedAccepted b)
  have hreprA : A = currentCylinder U (liftedAccepted a) := by
    simpa [a] using hreprU a
  have hreprB : B = currentCylinder U (liftedAccepted b) := by
    simpa [b] using hreprU b
  have haeA : (fun m => m ∈ A) =ᵐ[mu] (fun m => m ∈ AR) := by
    filter_upwards [haeAU] with m hm
    rw [hreprA]
    simpa [AR, L, reducedAccepted] using hm
  have haeB : (fun m => m ∈ B) =ᵐ[mu] (fun m => m ∈ BR) := by
    filter_upwards [haeBU] with m hm
    rw [hreprB]
    simpa [BR, L, reducedAccepted] using hm
  have hti : CurrentIsTranslationInvariant
      (H := Multiplicative (Site d)) mu :=
    infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta
  have haeBshift := (hti g).quasiMeasurePreserving.ae_eq_comp haeB
  have haeJoint :
      (fun m => m ∈ A ∩ (currentShift g) ⁻¹' B) =ᵐ[mu]
        (fun m => m ∈ AR ∩ (currentShift g) ⁻¹' BR) := by
    filter_upwards [haeA, haeBshift] with m hmA hmB
    change ((m ∈ A) ∧ currentShift g m ∈ B) =
      ((m ∈ AR) ∧ currentShift g m ∈ BR)
    exact congrArg₂ And hmA hmB
  have hmassA : mu.real A = mu.real AR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu) (s := A) (t := AR) haeA)
  have hmassB : mu.real B = mu.real BR := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu) (s := B) (t := BR) haeB)
  have hmassJoint :
      mu.real (A ∩ (currentShift g) ⁻¹' B) =
        mu.real (AR ∩ (currentShift g) ⁻¹' BR) := by
    unfold Measure.real
    exact congrArg ENNReal.toReal
      (measure_congr (μ := mu)
        (s := A ∩ (currentShift g) ⁻¹' B)
        (t := AR ∩ (currentShift g) ⁻¹' BR) haeJoint)
  have hcore := hmix (reducedAccepted a) haReduced
    (reducedAccepted b) hbReduced
  change abs (mu.real (A ∩ (currentShift g) ⁻¹' B) -
    mu.real A * mu.real B) < epsilon
  rw [hmassA, hmassB, hmassJoint]
  simpa [AR, BR, mu, L] using hcore


theorem infinitePlusCurrentMeasure_isErgodic {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    CurrentIsErgodic (H := Multiplicative (Site d))
      (infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) :=
  current_isErgodic_of_cylinderPairMixing
    (infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta)
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)

end StatMech.FrontierB
