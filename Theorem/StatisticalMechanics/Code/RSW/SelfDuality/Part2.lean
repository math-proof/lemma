/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.RSW.SelfDuality.Part2
open SimpleGraph Real


namespace StatMech

namespace RSW

open StatMech.Lattice


@[simp] theorem dualBC_free : dualBC .free = .wired := rfl

@[simp] theorem dualBC_wired : dualBC .wired = .free := rfl

@[simp] theorem dualBC_periodic : dualBC .periodic = .periodic := rfl


@[simp] theorem dualBC_dualBC (bc : BoundaryCondition) : dualBC (dualBC bc) = bc := by
  cases bc <;> rfl


theorem isOpen_iff_not_dualCross_open (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ω e = true ↔ ¬ dualConfig ω (crossEdge e) = true := by
  rw [Lattice.isOpen_iff_dual_isClosed]; simp [Bool.not_eq_true]


theorem dualCross_open_iff_closed (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : dualConfig ω (crossEdge e) = true ↔ ω e = false := by
  rw [Lattice.dual_isOpen_iff_isClosed, Equiv.symm_apply_apply]


theorem crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
  rintro ⟨h1, h2⟩
  rw [isOpen_iff_not_dualCross_open] at h1
  exact h1 h2


theorem ConfigSpace.edge_of_mem_openWalk {ω : ConfigSpace (Sym2 (Site 2))}
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y) {e : Sym2 (Site 2)}
    (he : e ∈ w.edges) : ω e = true := by
  have hmem : e ∈ (openSubgraph 2 ω).edgeSet := w.edges_subset_edgeSet he
  revert hmem
  refine Sym2.ind (fun a b hmem => ?_) e
  rw [SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2


theorem openWalk_blocks_dualWalk (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  crossingPair_incompatible ω e
    ⟨ConfigSpace.edge_of_mem_openWalk w he,
     ConfigSpace.edge_of_mem_openWalk w' he'⟩


theorem dualConfig_involutive (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) :=
  Lattice.dualConfig_dualConfig ω e

end RSW
end StatMech
