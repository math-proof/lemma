/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable instance sixVertexDefectLowerGraph_adjDecidable (n D : Nat) :
    DecidableRel (sixVertexDefectLowerGraph n D).Adj :=
  Classical.decRel _

end
end StatMech.FrontierD
