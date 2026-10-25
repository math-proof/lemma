/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part16


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem coordinateDiameterBound_empty {d R : ℕ} :
    (empty d).coordinateDiameterBound R := by
  intro x hx
  exact False.elim ((not_mem_empty x) hx)

theorem coordinateDiameterBound_mono_radius {d R S : ℕ} {P : PolymerSupport d}
    (hRS : R ≤ S) (hP : P.coordinateDiameterBound R) :
    P.coordinateDiameterBound S := by
  intro x hx y hy i
  exact le_trans (hP x hx y hy i) hRS

theorem coordinateDiameterBound_mono_support {d R : ℕ} {P Q : PolymerSupport d}
    (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q) (hQ : Q.coordinateDiameterBound R) :
    P.coordinateDiameterBound R := by
  intro x hx y hy i
  exact hQ x (hPQ hx) y (hPQ hy) i

theorem coordinateDiameterBound_of_containedInBox {d R : ℕ} {P : PolymerSupport d}
    (hP : P.containedInBox R) :
    P.coordinateDiameterBound (R + R) := by
  intro x hx y hy i
  exact le_trans (Int.natAbs_sub_le (x i) (y i))
    (Nat.add_le_add (hP x hx i) (hP y hy i))

theorem coordinateDiameterBound_translate {d R : ℕ} {P : PolymerSupport d} {v : Site d}
    (hP : P.coordinateDiameterBound R) :
    (P.translate v).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_translate P v x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_translate P v y).mp hy with ⟨y₀, hy₀, rfl⟩
  have hcoord : (x₀ + v) i - (y₀ + v) i = x₀ i - y₀ i := by
    change (x₀ i + v i) - (y₀ i + v i) = x₀ i - y₀ i
    ring
  rw [hcoord]
  exact hP x₀ hx₀ y₀ hy₀ i


theorem containedInBox_translate_neg_of_mem_of_coordinateDiameterBound
    {d R : ℕ} {P : PolymerSupport d} {a : Site d}
    (ha : a ∈ P) (hP : P.coordinateDiameterBound R) :
    (P.translate (-a)).containedInBox R := by
  intro x hx i
  rcases (mem_translate P (-a) x).mp hx with ⟨y, hy, rfl⟩
  have hcoord : (y + -a) i = y i - a i := by
    simp
    ring
  rw [hcoord]
  exact hP y hy a ha i


theorem exists_translate_containedInBox_of_nonempty_coordinateDiameterBound
    {d R : ℕ} {P : PolymerSupport d}
    (hne : P.carrier.Nonempty) (hP : P.coordinateDiameterBound R) :
    ∃ v : Site d, (P.translate v).containedInBox R := by
  rcases hne with ⟨a, ha⟩
  exact ⟨-a,
    containedInBox_translate_neg_of_mem_of_coordinateDiameterBound ha hP⟩


theorem coordinateDiameterBound_permuteCoordinates {d R : ℕ}
    {P : PolymerSupport d} (σ : Equiv.Perm (Fin d))
    (hP : P.coordinateDiameterBound R) :
    (P.permuteCoordinates σ).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_permuteCoordinates P σ x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_permuteCoordinates P σ y).mp hy with ⟨y₀, hy₀, rfl⟩
  exact hP x₀ hx₀ y₀ hy₀ (σ.symm i)


theorem coordinateDiameterBound_reflectCoordinates {d R : ℕ}
    {P : PolymerSupport d} (ε : CoordinateReflection d)
    (hP : P.coordinateDiameterBound R) :
    (P.reflectCoordinates ε).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_reflectCoordinates P ε x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_reflectCoordinates P ε y).mp hy with ⟨y₀, hy₀, rfl⟩
  by_cases hε : ε i
  · have hcoord :
        reflectCoordinatesSite ε x₀ i - reflectCoordinatesSite ε y₀ i =
          -(x₀ i - y₀ i) := by
      simp [reflectCoordinatesSite, hε]
      ring
    rw [hcoord, Int.natAbs_neg]
    exact hP x₀ hx₀ y₀ hy₀ i
  · simpa [reflectCoordinatesSite, hε] using hP x₀ hx₀ y₀ hy₀ i


theorem coordinateDiameterBound_cubicTransform {d R : ℕ}
    {P : PolymerSupport d} {v : Site d}
    (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d)
    (hP : P.coordinateDiameterBound R) :
    (P.cubicTransform v σ ε).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨x₀, hx₀, rfl⟩
  rcases (mem_cubicTransform P v σ ε y).mp hy with ⟨y₀, hy₀, rfl⟩
  have hbase := hP x₀ hx₀ y₀ hy₀ (σ.symm i)
  by_cases hε : ε i
  · have hcoord :
        cubicTransformSite v σ ε x₀ i -
            cubicTransformSite v σ ε y₀ i =
          -(x₀ (σ.symm i) - y₀ (σ.symm i)) := by
      simp [cubicTransformSite, reflectCoordinatesSite,
        permuteCoordinatesSite, hε]
      ring
    rw [hcoord, Int.natAbs_neg]
    exact hbase
  · have hcoord :
        cubicTransformSite v σ ε x₀ i -
            cubicTransformSite v σ ε y₀ i =
          x₀ (σ.symm i) - y₀ (σ.symm i) := by
      simp [cubicTransformSite, reflectCoordinatesSite,
        permuteCoordinatesSite, hε]
    rw [hcoord]
    exact hbase

theorem coordinateDiameterBound_union {d R : ℕ} {P Q : PolymerSupport d}
    (hP : P.coordinateDiameterBound R) (hQ : Q.coordinateDiameterBound R)
    (hCross : ∀ x ∈ P, ∀ y ∈ Q, ∀ i, (x i - y i).natAbs ≤ R) :
    (P ∪ Q).coordinateDiameterBound R := by
  intro x hx y hy i
  rcases (mem_union P Q x).mp hx with hxP | hxQ
  · rcases (mem_union P Q y).mp hy with hyP | hyQ
    · exact hP x hxP y hyP i
    · exact hCross x hxP y hyQ i
  · rcases (mem_union P Q y).mp hy with hyP | hyQ
    · have hsym : (x i - y i).natAbs = (y i - x i).natAbs := by
        have hneg : x i - y i = -(y i - x i) := by ring
        rw [hneg, Int.natAbs_neg]
      simpa [hsym] using hCross y hyP x hxQ i
    · exact hQ x hxQ y hyQ i

theorem coordinateDiameterBound_union_of_containedInBox {d R : ℕ}
    {P Q : PolymerSupport d} (hP : P.containedInBox R) (hQ : Q.containedInBox R) :
    (P ∪ Q).coordinateDiameterBound (R + R) :=
  coordinateDiameterBound_of_containedInBox (containedInBox_union_intro hP hQ)

end PolymerSupport
end Exact3D
end StatMech
