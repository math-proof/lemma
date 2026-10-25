/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open Filter MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem abs_map_real_sub_map_real_le_disagreement
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    [MeasurableEq Xi]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f g : Omega -> Xi) (hf : Measurable f) (hg : Measurable g)
    (A : Set Xi) (hA : MeasurableSet A) :
    abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤
      mu.real {z | f z ≠ g z} := by
  let F := f ⁻¹' A
  let G := g ⁻¹' A
  let D := {z | f z ≠ g z}
  have hF : MeasurableSet F := hA.preimage hf
  have hG : MeasurableSet G := hA.preimage hg
  have hD : MeasurableSet D := (measurableSet_eq_fun hf hg).compl
  have hFG : F ⊆ G ∪ D := by
    intro z hz
    by_cases heq : f z = g z
    · left
      simpa [F, G, heq] using hz
    · exact Or.inr heq
  have hGF : G ⊆ F ∪ D := by
    intro z hz
    by_cases heq : f z = g z
    · left
      simpa [F, G, heq] using hz
    · exact Or.inr heq
  have hleFG : mu.real F ≤ mu.real G + mu.real D :=
    (measureReal_mono hFG).trans (measureReal_union_le G D)
  have hleGF : mu.real G ≤ mu.real F + mu.real D :=
    (measureReal_mono hGF).trans (measureReal_union_le F D)
  rw [Measure.real, Measure.real,
    Measure.map_apply hf hA, Measure.map_apply hg hA]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    simpa only [F, G, D, Measure.real, add_comm] using hleFG
  · rw [sub_le_iff_le_add]
    simpa only [F, G, D, Measure.real, add_comm] using hleGF


theorem abs_map_real_sub_map_real_le_error
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f g : Omega -> Xi) (hf : Measurable f) (hg : Measurable g)
    (A : Set Xi) (hA : MeasurableSet A) (D : Set Omega)
    (hagree : ∀ z, z ∉ D -> (f z ∈ A ↔ g z ∈ A)) :
    abs ((Measure.map f mu).real A - (Measure.map g mu).real A) ≤
      mu.real D := by
  let F := f ⁻¹' A
  let G := g ⁻¹' A
  have hFG : F ⊆ G ∪ D := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · exact Or.inl ((hagree z hzD).mp hz)
  have hGF : G ⊆ F ∪ D := by
    intro z hz
    by_cases hzD : z ∈ D
    · exact Or.inr hzD
    · exact Or.inl ((hagree z hzD).mpr hz)
  have hleFG : mu.real F ≤ mu.real G + mu.real D :=
    (measureReal_mono hFG).trans (measureReal_union_le G D)
  have hleGF : mu.real G ≤ mu.real F + mu.real D :=
    (measureReal_mono hGF).trans (measureReal_union_le F D)
  rw [Measure.real, Measure.real,
    Measure.map_apply hf hA, Measure.map_apply hg hA]
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    simpa only [F, G, Measure.real, add_comm] using hleFG
  · rw [sub_le_iff_le_add]
    simpa only [F, G, Measure.real, add_comm] using hleGF


theorem ProbabilityMeasure.ext_of_pottsSpinCylinder
    {d q : Nat} (mu nu : ProbabilityMeasure (PottsConfig d q))
    (h : ∀ (sites : Finset (Site d))
      (colors : Set (∀ _x : sites, Fin q)),
      mu (cylinder (α := fun _ : Site d => Fin q) sites colors) =
        nu (cylinder (α := fun _ : Site d => Fin q) sites colors)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : Site d => Fin q))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨sites, colors, _, rfl⟩ := hC
    simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun z : NNReal => (z : ENNReal)) (h sites colors)
  · simp


end
end StatMech.FK
