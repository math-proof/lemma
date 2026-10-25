/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
open Finset BigOperators


namespace AlgebraicTopologyI

/-- Inserting a zero in the `i`-th coordinate of a point of the standard `(n+1)`-simplex
yields a point of the standard `(n+2)`-simplex: this is the `i`-th face inclusion at the
level of barycentric coordinates. -/
lemma faceMap_mem_stdSimplex (n : ℕ) (i : Fin (n + 2))
    (t : Fin (n + 1) → ℝ) (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
    Fin.insertNth i (0 : ℝ) t ∈ stdSimplex ℝ (Fin (n + 2)) := by
  obtain ⟨hnn, hsum⟩ := ht
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · simp [h, Fin.insertNth_apply_same]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simp [Fin.insertNth_apply_succAbove, hnn]
  · rw [Fin.sum_univ_succAbove _ i]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hsum]

end AlgebraicTopologyI
