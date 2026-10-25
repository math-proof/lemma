/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}


theorem oddPrismInternalEdge_not_isDiag
    (n : Nat) (q : OddPrismInternalIndex n) :
    ¬ (oddPrismInternalEdge n q).IsDiag := by
  rcases q with q | q
  · simp [oddPrismInternalEdge, Sym2.mk_isDiag_iff,
      RectangularPrismSite.mk.injEq]
  · rcases q with q | q <;>
      simp [oddPrismInternalEdge, Sym2.mk_isDiag_iff,
        RectangularPrismSite.mk.injEq]

@[simp] theorem oddPrismInternalGraph_edgeFinset (n : Nat)
    [Fintype (oddPrismInternalGraph n).edgeSet] :
    (oddPrismInternalGraph n).edgeFinset = oddPrismInternalEdges n := by
  ext e
  constructor
  · intro he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    simp only [oddPrismInternalGraph,
      SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff] at he'
    exact he'.1
  · intro he
    apply SimpleGraph.mem_edgeFinset.mpr
    rw [oddPrismInternalGraph, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨he, ?_⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    exact oddPrismInternalEdge_not_isDiag n q


end
end StatMech.FrontierA
