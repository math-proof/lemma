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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part11


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

theorem containedInBox_iff {d R : ℕ} {P : PolymerSupport d} :
    P.containedInBox R ↔ ∀ x ∈ P, x ∈ box d R :=
  Iff.rfl

@[simp] theorem containedInBox_empty {d R : ℕ} :
    (empty d).containedInBox R := by
  intro x hx
  exact False.elim ((not_mem_empty x) hx)

theorem containedInBox_mono_radius {d R S : ℕ} {P : PolymerSupport d}
    (hRS : R ≤ S) (hP : P.containedInBox R) :
    P.containedInBox S := by
  intro x hx
  exact coordinateRadiusBound_mono hRS (hP x hx)

theorem containedInBox_mono_support {d R : ℕ} {P Q : PolymerSupport d}
    (hPQ : ∀ {x : Site d}, x ∈ P → x ∈ Q) (hQ : Q.containedInBox R) :
    P.containedInBox R := by
  intro x hx
  exact hQ x (hPQ hx)

theorem containedInBox_translate {d R S : ℕ} {P : PolymerSupport d} {v : Site d}
    (hP : P.containedInBox R) (hv : coordinateRadiusBound S v) :
    (P.translate v).containedInBox (R + S) := by
  intro x hx
  rcases (mem_translate P v x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_add (hP y hy) hv


theorem containedInBox_permuteCoordinates {d R : ℕ} {P : PolymerSupport d}
    (σ : Equiv.Perm (Fin d)) (hP : P.containedInBox R) :
    (P.permuteCoordinates σ).containedInBox R := by
  intro x hx
  rcases (mem_permuteCoordinates P σ x).mp hx with ⟨y, hy, rfl⟩
  exact coordinateRadiusBound_permuteCoordinatesSite σ (hP y hy)


end PolymerSupport
end Exact3D
end StatMech
