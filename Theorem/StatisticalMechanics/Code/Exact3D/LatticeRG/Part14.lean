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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part14


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem cubicTransformSite_identity {d : ℕ} (x : Site d) :
    cubicTransformSite (0 : Site d) (Equiv.refl (Fin d))
      (fun _ : Fin d => false) x = x := by
  ext i
  simp [cubicTransformSite]

@[simp] theorem cubicTransformSite_comp {d : ℕ}
    (v w : Site d) (σ τ : Equiv.Perm (Fin d))
    (ε δ : CoordinateReflection d) (x : Site d) :
    cubicTransformSite w τ δ (cubicTransformSite v σ ε x) =
      cubicTransformSite
        (reflectCoordinatesSite δ (permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) x := by
  ext i
  by_cases hε : ε (τ.symm i) <;> by_cases hδ : δ i <;>
    simp [cubicTransformSite, reflectCoordinatesSite, permuteCoordinatesSite,
      hε, hδ, Bool.xor] <;>
    ring

theorem cubicTransformSite_injective {d : ℕ} (v : Site d)
    (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    Function.Injective (cubicTransformSite v σ ε) := by
  intro x y hxy
  have hreflect :
      reflectCoordinatesSite ε (permuteCoordinatesSite σ x) =
        reflectCoordinatesSite ε (permuteCoordinatesSite σ y) := by
    ext i
    have hcoord :
        (reflectCoordinatesSite ε (permuteCoordinatesSite σ x)) i + v i =
          (reflectCoordinatesSite ε (permuteCoordinatesSite σ y)) i + v i := by
      simpa [cubicTransformSite] using congrFun hxy i
    exact add_right_cancel hcoord
  exact permuteCoordinatesSite_injective σ
    (reflectCoordinatesSite_injective ε hreflect)


end PolymerSupport
end Exact3D
end StatMech
