/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortCircle


namespace StatMech.FrontierA

open Set SimpleGraph


noncomputable def KWAngularPortRadiusData.trimParameter
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (d : G.Dart) : ℝ :=
  (data.radius : ℝ) /
    ‖embedding.vertex d.snd - embedding.vertex d.fst‖

end StatMech.FrontierA
