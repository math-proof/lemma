/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part9
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


open MeasureTheory Filter

lemma intervalPatternRestriction_pattern (r : ℕ) (t : Finset (Site 1))
    (ht : (t : Set (Site 1)) ⊆ box 1 r) (sigma : ConfigSpace (Site 1)) :
    intervalPatternRestriction r t ht (intervalStatePattern r sigma) =
      fun x : t => sigma x.1 := by
  funext x
  unfold intervalPatternRestriction intervalStatePattern
  change boolEquivFin2.symm
      (boolEquivFin2 (sigma (site1 (-(r : ℤ) +
        (((box1EquivFin r) ⟨x.1, ht x.2⟩).val : ℤ))))) = sigma x.1
  rw [Equiv.symm_apply_apply]
  congr 2
  have hx := congrArg Subtype.val
    ((box1EquivFin r).symm_apply_apply ⟨x.1, ht x.2⟩)
  change site1 ((((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) - (r : ℤ)) = x.1 at hx
  change site1 (-(r : ℤ) +
    (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ)) = x.1
  rw [show -(r : ℤ) + (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) =
    (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) - (r : ℤ) by ring]
  exact hx

theorem map_finsetRestriction_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p))
    (t : Finset (Site 1)) :
    Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) mu =
      Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) nu := by
  let r := t.sup (fun x => (site1Coord x).natAbs)
  have ht : (t : Set (Site 1)) ⊆ box 1 r := by
    intro x hx
    rw [← site1_site1Coord x, site1_mem_box_iff]
    have hle : (site1Coord x).natAbs ≤ r := Finset.le_sup (f := fun y =>
      (site1Coord y).natAbs) hx
    have habs : |site1Coord x| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
    exact abs_le.mp habs
  let proj : ConfigSpace (Site 1) → (t → Bool) := fun sigma x => sigma x.1
  let recover : (Fin (2 * r + 1) → Fin 2) → (t → Bool) :=
    intervalPatternRestriction r t ht
  have hproj : Measurable proj := by
    apply measurable_pi_lambda
    intro x
    exact measurable_pi_apply _
  have hrecover : Measurable recover := measurable_of_finite _
  have hpattern := measurable_intervalStatePattern r
  have hmap := map_intervalStatePattern_eq_of_block_eq hblock r
  have hfac : recover ∘ intervalStatePattern r = proj := by
    funext sigma
    exact intervalPatternRestriction_pattern r t ht sigma
  change Measure.map proj mu = Measure.map proj nu
  calc
    Measure.map proj mu = Measure.map recover (Measure.map (intervalStatePattern r) mu) := by
      rw [Measure.map_map hrecover hpattern, hfac]
    _ = Measure.map recover (Measure.map (intervalStatePattern r) nu) := by rw [hmap]
    _ = Measure.map proj nu := by
      rw [Measure.map_map hrecover hpattern, hfac]

theorem measure_cylinder_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p))
    (t : Finset (Site 1)) (S : Set (t → Bool)) (hS : MeasurableSet S) :
    mu (cylinder t S) = nu (cylinder t S) := by
  have hproj : Measurable
      (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) := by
    apply measurable_pi_lambda
    intro x
    exact measurable_pi_apply _
  have hmap := map_finsetRestriction_eq_of_block_eq hblock t
  calc
    mu (cylinder t S) = (Measure.map
        (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) mu) S := by
      rw [Measure.map_apply hproj hS]
      rfl
    _ = (Measure.map
        (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) nu) S := by
      rw [hmap]
    _ = nu (cylinder t S) := by
      rw [Measure.map_apply hproj hS]
      rfl


theorem oneDim_isDLRState_unique (beta h : ℝ)
    (mu nu : Measure (ConfigSpace (Site 1))) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (hmu : IsDLRState 1 beta h mu)
    (hnu : IsDLRState 1 beta h nu) : mu = nu := by
  have hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p) := by
    intro r p
    rw [dlr_blockStateEvent_real_eq_limit beta h mu hmu r p,
      dlr_blockStateEvent_real_eq_limit beta h nu hnu r p]
  apply ext_of_generate_finite (measurableCylinders (fun _ : Site 1 => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro A hA
    rw [mem_measurableCylinders] at hA
    obtain ⟨t, S, hS, rfl⟩ := hA
    exact measure_cylinder_eq_of_block_eq hblock t S hS
  · rw [measure_univ, measure_univ]


end StatMech.FrontierB
