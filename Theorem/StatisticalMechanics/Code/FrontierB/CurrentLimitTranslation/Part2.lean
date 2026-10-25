/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
import Def.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation.Part2
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


theorem currentLocalParity_shiftPattern
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (a : ↑S -> Nat) :
    currentLocalParity (currentShiftPattern g S a) =
      currentShiftPattern g S (currentLocalParity a) := by
  rfl


theorem preimage_currentCylinder_singleton_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (a : ↑S -> Nat) :
    (currentShift g) ⁻¹' currentCylinder S {a} =
      currentCylinder (currentShiftFinset g S)
        {currentShiftPattern g S a} := by
  ext m
  simp only [Set.mem_preimage, currentCylinder, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro h
    funext e
    have he := congrFun h (currentShiftFinsetEquiv g S e)
    simpa [restrictCurrent, currentShift, currentShiftPattern] using he
  · intro h
    funext e
    have he := congrFun h ((currentShiftFinsetEquiv g S).symm e)
    simpa [restrictCurrent, currentShift, currentShiftPattern] using he


theorem currentShiftFinset_lattice
    (d : Nat) (g : Multiplicative (Site d))
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (↑(currentShiftFinset g S) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  have hfedge := hS hf
  induction f using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at hfedge
      rw [Percolation.smul_sym2_mk, SimpleGraph.mem_edgeSet]
      exact (Percolation.hyper_adj_smul g⁻¹ x y).2 hfedge


theorem preimage_currentParityAvoidCylinder_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (F : Finset E) :
    (currentShift g) ⁻¹' currentParityAvoidCylinder F =
      currentParityAvoidCylinder (currentShiftFinset g F) := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder]
  constructor
  · intro h e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact h f hf
  · intro h e he
    have hs : g⁻¹ • e ∈ currentShiftFinset g F :=
      Finset.mem_image_of_mem _ he
    exact h (g⁻¹ • e) hs


theorem edgeSpinSum_shift
    (d : Nat) (g : Multiplicative (Site d))
    (F : Finset (Sym2 (Site d))) (omega : ConfigSpace (Site d)) :
    edgeSpinSum F (ConfigSpace.shift g omega) =
      edgeSpinSum (currentShiftFinset g F) omega := by
  unfold edgeSpinSum currentShiftFinset
  rw [Finset.sum_image (fun a _ b _ hab => MulAction.injective g⁻¹ hab)]
  apply Finset.sum_congr rfl
  intro e he
  simpa using iptp_bond_shift g omega (g⁻¹ • e)


theorem integral_exp_neg_edgeSpinSum_shift
    (d : Nat) (beta : Real)
    (mu : Measure (ConfigSpace (Site d)))
    (hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu)
    (g : Multiplicative (Site d)) (F : Finset (Sym2 (Site d))) :
    (∫ omega, Real.exp (-beta * edgeSpinSum
        (currentShiftFinset g F) omega) ∂mu) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu := by
  let e : ConfigSpace (Site d) ≃ᵐ ConfigSpace (Site d) :=
    { toEquiv :=
        { toFun := ConfigSpace.shift g
          invFun := ConfigSpace.shift g⁻¹
          left_inv := fun omega => by
            exact congrFun (ConfigSpace.shift_inv_comp g) omega
          right_inv := fun omega => by
            exact congrFun (ConfigSpace.shift_comp_inv g) omega }
      measurable_toFun := ConfigSpace.measurable_shift g
      measurable_invFun := ConfigSpace.measurable_shift g⁻¹ }
  have hmp : MeasurePreserving e mu mu := hti g
  have hint := hmp.integral_comp'
    (fun omega => Real.exp (-beta * edgeSpinSum F omega))
  change (∫ omega, Real.exp (-beta * edgeSpinSum F
      (ConfigSpace.shift g omega)) ∂mu) =
    ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂mu at hint
  simpa only [edgeSpinSum_shift] using hint


theorem infinitePlusCurrentMeasure_parityAvoid_eq
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infinitePlusCurrentMeasure d beta hbeta.le : Measure _)
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  have hcurrent := (plusBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal
    F {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hcurrent
  exact tendsto_nhds_unique hcurrent
    (plusBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta.le F hF)


theorem infiniteFreeCurrentMeasure_parityAvoid_eq
    (d : Nat) (beta : Real) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _)
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  have hcurrent := (freeBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal
    F {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hcurrent
  exact tendsto_nhds_unique hcurrent
    (freeBoxCurrentMeasure_parityAvoid_full_tendsto d beta hbeta.le F hF)


theorem finiteParityPMF_shiftPattern
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (beta : Real) (hbeta : 0 < beta)
    (odd : ↑S -> Bool) (a : ↑S -> Nat) :
    finiteParityPMF (currentShiftFinset g S) beta hbeta
        (currentShiftPattern g S odd) (currentShiftPattern g S a) =
      finiteParityPMF S beta hbeta odd a := by
  rw [finiteParityPMF_apply, finiteParityPMF_apply]
  congr 1
  unfold finiteParityKernel currentShiftPattern
  apply Fintype.prod_equiv (currentShiftFinsetEquiv g S)
  intro e
  rfl


theorem preimage_currentParityPatternCylinder_currentShift
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (odd : ↑S -> Bool) :
    (currentShift g) ⁻¹' currentParityPatternCylinder S odd =
      currentParityPatternCylinder (currentShiftFinset g S)
        (currentShiftPattern g S odd) := by
  ext m
  simp only [Set.mem_preimage, currentParityPatternCylinder]
  constructor
  · intro h
    funext e
    have he := congrFun h (currentShiftFinsetEquiv g S e)
    simpa [currentLocalParity, restrictCurrent, currentShift,
      currentShiftPattern] using he
  · intro h
    funext e
    have he := congrFun h ((currentShiftFinsetEquiv g S).symm e)
    simpa [currentLocalParity, restrictCurrent, currentShift,
      currentShiftPattern] using he


end StatMech.FrontierB
