/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part92
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_dualReflectOpenHom
    (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (fci_faceDualConfig omega) →g
      openSubgraph 2 (rlc_dualReflectConfig omega) where
  toFun := rlc_dualReflect
  map_rel' := by
    intro x y hxy
    rw [openSubgraph_adj] at hxy ⊢
    refine ⟨(rlc_adj_dualReflect x y).mp hxy.1, ?_⟩
    rw [rlc_dualReflectConfig_mk]
    exact hxy.2


noncomputable def rlc_dualReflectOpenWalk
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (w : (openSubgraph 2 (fci_faceDualConfig omega)).Walk x y) :
    (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk
      (rlc_dualReflect x) (rlc_dualReflect y) :=
  w.map (rlc_dualReflectOpenHom omega)

end Universality
end StatMech
