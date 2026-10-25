/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem measurable_extendWiredEdge (d n : Nat) :
    Measurable (extendWiredEdge d n) :=
  Measurable.of_discrete

theorem extendWiredEdge_eq_of_range
    {d : Nat} (n : Nat) (be : Sym2 (boxVerts d n))
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    extendWiredEdge d n omega (edgeIncl d n be) = omega be := by
  unfold extendWiredEdge
  have hmem : edgeIncl d n be ∈ Set.range (edgeIncl d n) := ⟨be, rfl⟩
  rw [dif_pos hmem, edgeIncl_injective d n hmem.choose_spec]

theorem extendWiredEdge_eq_true_of_not_range
    {d : Nat} (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    {e : Sym2 (Site d)} (he : e ∉ Set.range (edgeIncl d n)) :
    extendWiredEdge d n omega e = true := by
  simp only [extendWiredEdge, dif_neg he]


theorem boxRestrict_extendWiredEdge (d n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    boxRestrict d n (extendWiredEdge d n omega) = omega := by
  funext e
  exact extendWiredEdge_eq_of_range n e omega


theorem extendWiredEdge_restrict_eq_extendEdge_restrict
    {d : Nat} (n : Nat) (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (edges : Finset (Sym2 (Site d)))
    (hedges : ∀ e ∈ edges, e ∈ Set.range (edgeIncl d n)) :
    edges.restrict (extendWiredEdge d n omega) =
      edges.restrict (extendEdge d n omega) := by
  funext e
  obtain ⟨be, hbe⟩ := hedges e e.2
  change extendWiredEdge d n omega e = extendEdge d n omega e
  rw [← hbe, extendWiredEdge_eq_of_range, extendEdge_eq_of_range]


end StatMech.FK
