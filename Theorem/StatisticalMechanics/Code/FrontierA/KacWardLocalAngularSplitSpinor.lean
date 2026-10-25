/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


theorem kwLocalPortRoot_sq_of_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    data.root q ^ 2 = -(data.root p ^ 2) := by
  have hq : q = kwPortOfDart G (kwDartOfPort G p).symm := by
    apply kwDartOfPort_injective G
    simpa using hmatching
  rw [hq, data.root_sq_symm]
  simp


end StatMech.FrontierA
