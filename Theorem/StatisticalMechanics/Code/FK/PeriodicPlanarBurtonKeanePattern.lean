/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeanePattern.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Theorem.StatisticalMechanics.Code.Percolation.TreeExteriorAmalgam
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeanePattern
open MeasureTheory Set SimpleGraph Finset


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type} [Countable V] [DecidableEq V]

theorem PeriodicGraph.mem_incidentEdgeFinset_mk
    (P : PeriodicGraph V) (K : Finset V) (x y : V) :
    s(x, y) ∈ P.incidentEdgeFinset K ↔
      P.graph.Adj x y ∧ (x ∈ K ∨ y ∈ K) := by
  classical
  letI : P.graph.LocallyFinite := P.locallyFinite
  simp only [PeriodicGraph.incidentEdgeFinset, Finset.mem_biUnion,
    Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hzK, w, hzw, heq⟩
    simp only [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hzw, Or.inl hzK⟩
    · exact ⟨hzw.symm, Or.inr hzK⟩
  · rintro ⟨hxy, hxK | hyK⟩
    · exact ⟨x, hxK, y, hxy, rfl⟩
    · exact ⟨y, hyK, x, hxy.symm, by simp⟩

end StatMech.FK.PeriodicPlanar
