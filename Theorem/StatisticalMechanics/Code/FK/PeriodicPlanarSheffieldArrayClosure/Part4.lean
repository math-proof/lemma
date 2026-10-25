/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem int_le_nat_of_toNat_le_array {x : Int} {n : Nat}
    (h : x.toNat ≤ n) : x ≤ n := by
  by_cases hx : 0 ≤ x
  · have h' : (x.toNat : Int) ≤ (n : Int) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hx] at h'
  · omega


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences
      family.fullVerticalRequirement family.fullHorizontalRequirement
  refine ⟨horizontal, vertical, hh, hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hhv n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hhv n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hhv n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hhv n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hvh n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hvh n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hvh n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hvh n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins_with_requirements
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
      (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) := by
  let verticalStep : Nat → Nat := fun h ↦
    max (family.horizontalRadiusRequirement E h) (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦
    max (family.verticalRadiusRequirement E v) (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  refine ⟨horizontal, vertical, hh, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (Nat.le_max_right _ _).trans (hhv n)
  · intro n
    exact (Nat.le_max_right _ _).trans (hvh n)
  · intro n
    have hreq : family.horizontalRadiusRequirement E (horizontal n) ≤
        vertical n := (Nat.le_max_left _ _).trans (hhv n)
    have hle : (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_left _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.horizontalRadiusRequirement E (horizontal n) ≤
        vertical n := (Nat.le_max_left _ _).trans (hhv n)
    have hle : (((family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_right _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.verticalRadiusRequirement E (vertical n) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
    have hle : (((family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.verticalRadiusRequirement E (vertical n) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
    have hle : (((family.radiusTop (vertical n) : Int) +
        family.baseTop 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) := (Nat.le_max_right _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega


theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_requirements
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
      (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  let verticalStep : Nat → Nat := fun h ↦
    max (family.fullVerticalRequirement E h) (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦
    max (family.fullHorizontalRequirement E v) (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  have hV (n : Nat) : family.fullVerticalRequirement E (horizontal n) ≤
      vertical n := (Nat.le_max_left _ _).trans (hhv n)
  have hH (n : Nat) : family.fullHorizontalRequirement E (vertical n) ≤
      horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
  refine ⟨horizontal, vertical, hh, hv,
    fun n ↦ (Nat.le_max_right _ _).trans (hhv n),
    fun n ↦ (Nat.le_max_right _ _).trans (hvh n),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega


end StatMech.FK.PeriodicPlanar
