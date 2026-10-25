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
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part7


namespace StatMech

namespace Exact3D

open StatMech.Lattice


namespace PolymerSupport

@[simp] theorem mem_translate {d : ℕ} (P : PolymerSupport d) (v x : Site d) :
    x ∈ P.translate v ↔ ∃ y, y ∈ P ∧ y + v = x := by
  classical
  change x ∈ P.carrier.image (fun y => y + v) ↔
    ∃ y, y ∈ P.carrier ∧ y + v = x
  exact Finset.mem_image

theorem mem_translate_iff_sub_mem {d : ℕ} (P : PolymerSupport d) (v x : Site d) :
    x ∈ P.translate v ↔ x - v ∈ P := by
  constructor
  · intro hx
    rcases (mem_translate P v x).mp hx with ⟨y, hy, rfl⟩
    have h : y + v - v = y := by
      ext i
      simp
    simpa [h] using hy
  · intro hx
    rw [mem_translate]
    refine ⟨x - v, hx, ?_⟩
    ext i
    simp

@[simp] theorem empty_translate {d : ℕ} (v : Site d) :
    (empty d).translate v = empty d := by
  ext x
  simp [translate, empty]

@[simp] theorem translate_zero {d : ℕ} (P : PolymerSupport d) :
    P.translate (0 : Site d) = P := by
  ext x
  simp [translate]

@[simp] theorem translate_translate {d : ℕ} (P : PolymerSupport d) (v w : Site d) :
    (P.translate v).translate w = P.translate (v + w) := by
  ext x
  simp [translate, add_assoc]

@[simp] theorem translate_card {d : ℕ} (P : PolymerSupport d) (v : Site d) :
    (P.translate v).carrier.card = P.carrier.card := by
  change (P.carrier.image fun x => x + v).card = P.carrier.card
  exact Finset.card_image_of_injective P.carrier (by
    intro x y hxy
    ext i
    have hcoord : x i + v i = y i + v i := by
      simpa using congrFun hxy i
    exact add_right_cancel hcoord)


end PolymerSupport
end Exact3D
end StatMech
