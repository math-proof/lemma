/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part12
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


@[simp] theorem innerRestrict_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    innerRestrict d n (crossExt d n ω) = ω := by
  funext e; rw [innerRestrict, crossExt_innerEdge]


theorem crossExt_innerRestrict_of_agreesOff (d n : ℕ)
    {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
    (hρ : AgreesOff (innerEdgeFinset d n) (fun _ => false) ρ) :
    crossExt d n (innerRestrict d n ρ) = ρ := by
  funext e
  unfold crossExt
  split
  · rename_i hmem
    show innerRestrict d n ρ hmem.choose = ρ e
    rw [innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm


theorem agreesOff_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    AgreesOff (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω) := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact crossExt_eq_false_of_not_range d n ω he


end FK
end StatMech
