/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
import Inductive.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDirectedTorusEdge

def tail {T : EvenTorus} : SixVertexDirectedTorusEdge T -> T.Vertex
  | .horizontal base true => base
  | .horizontal base false =>
      (finitePeriodicSucc T.width_pos base.1, base.2)
  | .vertical base true => base
  | .vertical base false =>
      (base.1, finitePeriodicSucc T.height_pos base.2)

def head {T : EvenTorus} : SixVertexDirectedTorusEdge T -> T.Vertex
  | .horizontal base true =>
      (finitePeriodicSucc T.width_pos base.1, base.2)
  | .horizontal base false => base
  | .vertical base true =>
      (base.1, finitePeriodicSucc T.height_pos base.2)
  | .vertical base false => base

def physical {T : EvenTorus} :
    SixVertexDirectedTorusEdge T -> Bool × T.Vertex
  | .horizontal base _ => (false, base)
  | .vertical base _ => (true, base)

def horizontalFlow {T : EvenTorus}
    (edge : SixVertexDirectedTorusEdge T) (v : T.Vertex) : Int :=
  match edge with
  | .horizontal base positive =>
      if v = base then if positive then 1 else -1 else 0
  | .vertical _ _ => 0

def verticalFlow {T : EvenTorus}
    (edge : SixVertexDirectedTorusEdge T) (v : T.Vertex) : Int :=
  match edge with
  | .horizontal _ _ => 0
  | .vertical base positive =>
      if v = base then if positive then 1 else -1 else 0

end SixVertexDirectedTorusEdge
end
end StatMech.FrontierD
