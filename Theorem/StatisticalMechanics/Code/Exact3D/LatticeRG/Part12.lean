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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part12


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem reflectCoordinatesSite_false {d : ℕ} (x : Site d) :
    reflectCoordinatesSite (fun _ : Fin d => false) x = x := by
  ext i
  simp [reflectCoordinatesSite]

@[simp] theorem reflectCoordinatesSite_reflectCoordinatesSite {d : ℕ}
    (ε δ : CoordinateReflection d) (x : Site d) :
    reflectCoordinatesSite δ (reflectCoordinatesSite ε x) =
      reflectCoordinatesSite (fun i => Bool.xor (ε i) (δ i)) x := by
  ext i
  by_cases hε : ε i <;> by_cases hδ : δ i <;>
    simp [reflectCoordinatesSite, hε, hδ, Bool.xor]

theorem reflectCoordinatesSite_injective {d : ℕ} (ε : CoordinateReflection d) :
    Function.Injective (reflectCoordinatesSite ε) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy i
  by_cases hε : ε i
  · have hneg := congrArg Neg.neg hcoord
    simpa [reflectCoordinatesSite, hε] using hneg
  · simpa [reflectCoordinatesSite, hε] using hcoord


end PolymerSupport
end Exact3D
end StatMech
