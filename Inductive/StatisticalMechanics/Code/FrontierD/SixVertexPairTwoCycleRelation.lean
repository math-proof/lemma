/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6


namespace StatMech.FrontierD

noncomputable section

inductive SixVertexDirectedTorusEdge (T : EvenTorus) where
  | horizontal (base : T.Vertex) (positive : Bool)
  | vertical (base : T.Vertex) (positive : Bool)

end
end StatMech.FrontierD
