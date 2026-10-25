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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part15


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem mem_cubicTransform {d : ℕ}
    (P : PolymerSupport d) (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) (x : Site d) :
    x ∈ P.cubicTransform v σ ε ↔
      ∃ y, y ∈ P ∧ cubicTransformSite v σ ε y = x := by
  classical
  change x ∈ P.carrier.image (cubicTransformSite v σ ε) ↔
    ∃ y, y ∈ P.carrier ∧ cubicTransformSite v σ ε y = x
  exact Finset.mem_image

@[simp] theorem cubicTransform_card {d : ℕ} (P : PolymerSupport d)
    (v : Site d) (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    (P.cubicTransform v σ ε).carrier.card = P.carrier.card := by
  change (P.carrier.image (cubicTransformSite v σ ε)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (cubicTransformSite_injective v σ ε)

@[simp] theorem cubicTransform_identity {d : ℕ} (P : PolymerSupport d) :
    P.cubicTransform (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) = P := by
  ext x
  simp [cubicTransform]

@[simp] theorem cubicTransform_cubicTransform {d : ℕ}
    (P : PolymerSupport d) (v w : Site d) (σ τ : Equiv.Perm (Fin d))
    (ε δ : CoordinateReflection d) :
    (P.cubicTransform v σ ε).cubicTransform w τ δ =
      P.cubicTransform
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
  ext x
  constructor
  · intro hx
    rcases (mem_cubicTransform (P.cubicTransform v σ ε) w τ δ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_cubicTransform P v σ ε y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_cubicTransform P
      (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
      (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i))
      (cubicTransformSite w τ δ (cubicTransformSite v σ ε z))).mpr
      ⟨z, hz, (cubicTransformSite_comp v w σ τ ε δ z).symm⟩
  · intro hx
    rcases (mem_cubicTransform P
      (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
      (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) x).mp hx with
      ⟨z, hz, rfl⟩
    exact (mem_cubicTransform (P.cubicTransform v σ ε) w τ δ
      (cubicTransformSite
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) z)).mpr
      ⟨cubicTransformSite v σ ε z,
        (mem_cubicTransform P v σ ε (cubicTransformSite v σ ε z)).mpr
          ⟨z, hz, rfl⟩,
        cubicTransformSite_comp v w σ τ ε δ z⟩

@[simp] theorem cubicTransform_inverse {d : ℕ}
    (P : PolymerSupport d) (v : Site d) (σ : Equiv.Perm (Fin d))
    (ε : CoordinateReflection d) :
    (P.cubicTransform v σ ε).cubicTransform
      (cubicInverseTranslation v σ ε) σ.symm (fun i => ε (σ i)) = P := by
  rw [cubicTransform_cubicTransform]
  have hsign :
      (fun i : Fin d => Bool.xor (ε (σ.symm.symm i)) ((fun i => ε (σ i)) i)) =
        (fun _ : Fin d => false) := by
    funext i
    by_cases hε : ε (σ i) <;>
      simp [hε, Bool.xor]
  rw [hsign]
  simp [cubicInverseTranslation]


theorem containedInBox_cubicTransform {d R S : ℕ} {P : PolymerSupport d}
    {v : Site d} (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d)
    (hP : P.containedInBox R) (hv : coordinateRadiusBound S v) :
    (P.cubicTransform v σ ε).containedInBox (R + S) := by
  intro x hx
  rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_add
    (coordinateRadiusBound_reflectCoordinatesSite ε
      (coordinateRadiusBound_permuteCoordinatesSite σ (hP y hy))) hv

theorem containedInBox_union {d R : ℕ} (P Q : PolymerSupport d) :
    (P ∪ Q).containedInBox R ↔ P.containedInBox R ∧ Q.containedInBox R := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x ((mem_union P Q x).mpr (Or.inl hx))
    · intro x hx
      exact h x ((mem_union P Q x).mpr (Or.inr hx))
  · rintro ⟨hP, hQ⟩ x hx
    rcases (mem_union P Q x).mp hx with hxP | hxQ
    · exact hP x hxP
    · exact hQ x hxQ

theorem containedInBox_union_intro {d R : ℕ} {P Q : PolymerSupport d}
    (hP : P.containedInBox R) (hQ : Q.containedInBox R) :
    (P ∪ Q).containedInBox R :=
  (containedInBox_union P Q).mpr ⟨hP, hQ⟩


end PolymerSupport
end Exact3D
end StatMech
