/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedSimpleArc.firstIndex {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : Fin arc.length :=
  ⟨0, arc.length_pos⟩

def SixVertexDirectedSimpleArc.lastIndex {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : Fin arc.length :=
  ⟨arc.length - 1, by
    have := arc.length_pos
    omega⟩

def SixVertexDirectedSimpleArc.start {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : T.Vertex :=
  (arc.edge arc.firstIndex).tail

def SixVertexDirectedSimpleArc.finish {T : EvenTorus}
    (arc : SixVertexDirectedSimpleArc T) : T.Vertex :=
  (arc.edge arc.lastIndex).head


end
end StatMech.FrontierD
