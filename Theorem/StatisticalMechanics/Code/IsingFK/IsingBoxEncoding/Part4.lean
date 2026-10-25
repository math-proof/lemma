/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section Lattice

variable {d : ℕ}


theorem isingSpin_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) (v : boxVerts d (n + 1)) :
    isingSpin (latToBox d n τ v) = spin (glue (plusField d) τ) (v : Site d) := by
  unfold spin
  by_cases h : (v : Site d) ∈ box d n
  · rw [latToBox, dif_pos h, glue_mem _ _ h]
    unfold bToF isingSpin
    cases hb : τ ⟨v, h⟩ <;> simp
  · rw [latToBox, dif_neg h, glue_not_mem _ _ h]
    unfold plusField isingSpin
    simp


theorem boundaryFixed_latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) (latToBox d n τ) := by
  intro v hv
  rw [boxBoundary, mem_vertexBoundary] at hv
  have hnotin : (v : Site d) ∉ box d n := by simpa using hv.2
  rw [latToBox, dif_neg hnotin]


end Lattice
end IsingFK
end StatMech
