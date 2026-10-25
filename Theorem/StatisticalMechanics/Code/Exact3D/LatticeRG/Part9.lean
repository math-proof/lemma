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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part9


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem mem_permuteCoordinates {d : ℕ}
    (P : PolymerSupport d) (σ : Equiv.Perm (Fin d)) (x : Site d) :
    x ∈ P.permuteCoordinates σ ↔
      ∃ y, y ∈ P ∧ permuteCoordinatesSite σ y = x := by
  classical
  change x ∈ P.carrier.image (permuteCoordinatesSite σ) ↔
    ∃ y, y ∈ P.carrier ∧ permuteCoordinatesSite σ y = x
  exact Finset.mem_image

@[simp] theorem permuteCoordinates_refl {d : ℕ} (P : PolymerSupport d) :
    P.permuteCoordinates (Equiv.refl (Fin d)) = P := by
  ext x
  simp [permuteCoordinates]

@[simp] theorem permuteCoordinates_trans {d : ℕ}
    (P : PolymerSupport d) (σ τ : Equiv.Perm (Fin d)) :
    (P.permuteCoordinates σ).permuteCoordinates τ =
      P.permuteCoordinates (σ.trans τ) := by
  ext x
  constructor
  · intro hx
    rcases (mem_permuteCoordinates (P.permuteCoordinates σ) τ x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_permuteCoordinates P σ y).mp hy with ⟨z, hz, rfl⟩
    exact (mem_permuteCoordinates P (σ.trans τ)
      (permuteCoordinatesSite τ (permuteCoordinatesSite σ z))).mpr ⟨z, hz, rfl⟩
  · intro hx
    rcases (mem_permuteCoordinates P (σ.trans τ) x).mp hx with ⟨z, hz, rfl⟩
    exact (mem_permuteCoordinates (P.permuteCoordinates σ) τ
      (permuteCoordinatesSite (σ.trans τ) z)).mpr
      ⟨permuteCoordinatesSite σ z,
        (mem_permuteCoordinates P σ (permuteCoordinatesSite σ z)).mpr
          ⟨z, hz, rfl⟩,
        rfl⟩

@[simp] theorem permuteCoordinates_card {d : ℕ}
    (P : PolymerSupport d) (σ : Equiv.Perm (Fin d)) :
    (P.permuteCoordinates σ).carrier.card = P.carrier.card := by
  change (P.carrier.image (permuteCoordinatesSite σ)).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier
    (permuteCoordinatesSite_injective σ)


end PolymerSupport
end Exact3D
end StatMech
