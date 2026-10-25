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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part13


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem mem_reflectCoordinates {d : ℕ}
    (P : PolymerSupport d) (ε : CoordinateReflection d) (x : Site d) :
    x ∈ P.reflectCoordinates ε ↔
      ∃ y, y ∈ P ∧ reflectCoordinatesSite ε y = x := by
  classical
  change x ∈ P.carrier.image (reflectCoordinatesSite ε) ↔
    ∃ y, y ∈ P.carrier ∧ reflectCoordinatesSite ε y = x
  exact Finset.mem_image

@[simp] theorem reflectCoordinates_false {d : ℕ} (P : PolymerSupport d) :
    P.reflectCoordinates (fun _ : Fin d => false) = P := by
  ext x
  simp [reflectCoordinates]

@[simp] theorem reflectCoordinates_reflectCoordinates {d : ℕ}
    (P : PolymerSupport d) (ε δ : CoordinateReflection d) :
    (P.reflectCoordinates ε).reflectCoordinates δ =
      P.reflectCoordinates (fun i => Bool.xor (ε i) (δ i)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_reflectCoordinates (P.reflectCoordinates ε) δ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_reflectCoordinates P ε y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_reflectCoordinates P (fun i => Bool.xor (ε i) (δ i))
      (reflectCoordinatesSite δ (reflectCoordinatesSite ε z))).mpr
      ⟨z, hz, (reflectCoordinatesSite_reflectCoordinatesSite ε δ z).symm⟩
  · intro hx
    rcases (mem_reflectCoordinates P (fun i => Bool.xor (ε i) (δ i)) x).mp hx with
      ⟨z, hz, rfl⟩
    exact (mem_reflectCoordinates (P.reflectCoordinates ε) δ
      (reflectCoordinatesSite (fun i => Bool.xor (ε i) (δ i)) z)).mpr
      ⟨reflectCoordinatesSite ε z,
        (mem_reflectCoordinates P ε (reflectCoordinatesSite ε z)).mpr
          ⟨z, hz, rfl⟩,
        reflectCoordinatesSite_reflectCoordinatesSite ε δ z⟩

@[simp] theorem reflectCoordinates_card {d : ℕ}
    (P : PolymerSupport d) (ε : CoordinateReflection d) :
    (P.reflectCoordinates ε).carrier.card = P.carrier.card := by
  change (P.carrier.image (reflectCoordinatesSite ε)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (reflectCoordinatesSite_injective ε)


theorem coordinateRadiusBound_reflectCoordinatesSite {d R : ℕ}
    {x : Site d} (ε : CoordinateReflection d)
    (hx : coordinateRadiusBound R x) :
    coordinateRadiusBound R (reflectCoordinatesSite ε x) := by
  intro i
  by_cases hε : ε i
  · simpa [reflectCoordinatesSite, hε] using hx i
  · simpa [reflectCoordinatesSite, hε] using hx i


theorem containedInBox_reflectCoordinates {d R : ℕ} {P : PolymerSupport d}
    (ε : CoordinateReflection d) (hP : P.containedInBox R) :
    (P.reflectCoordinates ε).containedInBox R := by
  intro x hx
  rcases (mem_reflectCoordinates P ε x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_reflectCoordinatesSite ε (hP y hy)


end PolymerSupport
end Exact3D
end StatMech
