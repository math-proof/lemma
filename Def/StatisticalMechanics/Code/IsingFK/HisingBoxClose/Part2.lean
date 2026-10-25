/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}


noncomputable def boxToLat (d n : ℕ) (σ : boxVerts d (n + 1) → Fin 2) :
    {x // x ∈ box d n} → Bool :=
  fun x => fToB (σ ⟨x.1, box_subset_succ d n x.2⟩)


noncomputable def hbx_latBoxEquiv (d n : ℕ) :
    ({x // x ∈ box d n} → Bool) ≃
      {σ : boxVerts d (n + 1) → Fin 2 // BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ} where
  toFun τ := ⟨latToBox d n τ, boundaryFixed_latToBox d n τ⟩
  invFun σ := boxToLat d n σ.1
  left_inv τ := by
    funext x
    show boxToLat d n (latToBox d n τ) x = τ x
    unfold boxToLat latToBox
    rw [dif_pos x.2, hbx_fToB_bToF]
  right_inv σ := by
    apply Subtype.ext
    funext v
    show latToBox d n (boxToLat d n σ.1) v = σ.1 v
    unfold latToBox boxToLat
    by_cases h : (v : Site d) ∈ box d n
    · rw [dif_pos h, hbx_bToF_fToB]
    · rw [dif_neg h]; exact (σ.2 v ((hbx_boxBoundary_succ_iff d n v).mpr h)).symm


end IsingFK
end StatMech
