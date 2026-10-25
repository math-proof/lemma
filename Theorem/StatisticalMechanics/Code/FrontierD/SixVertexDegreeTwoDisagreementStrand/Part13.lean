/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part14
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_map_sixVertexDegreeTwoOrderedAllStrands
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (f : SixVertexOrientedDisagreementDart omega eta → Int) :
    ((sixVertexDegreeTwoOrderedAllStrands
      homega heta hdegree).map f).sum = ∑ d, f d :=
  sum_map_permOrderedAllCycles
    (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree)
    (sixVertexOrientedDegreeTwoStrandSuccessor_support
      homega heta hdegree) f

end
end StatMech.FrontierD
