/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part6
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


@[simp] theorem PeriodicGraph.extendEdge_edgeIncl (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n)))
    (e : Sym2 (P.OrbitVertex n)) :
    P.extendEdge n omega (P.edgeIncl n e) = omega e := by
  unfold PeriodicGraph.extendEdge
  have hmem : P.edgeIncl n e ∈ Set.range (P.edgeIncl n) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact P.edgeIncl_injective n hmem.choose_spec

theorem PeriodicGraph.monotone_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Monotone (P.extendEdge n) := by
  intro omega eta home e
  unfold PeriodicGraph.extendEdge
  split
  · exact home _
  · exact le_refl false

theorem PeriodicGraph.measurable_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Measurable (P.extendEdge n) :=
  Measurable.of_discrete


end PeriodicPlanar
end FK
end StatMech
