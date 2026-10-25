/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectDevelopedThreeByOneRect (n : Nat) : Set (Site 2) :=
  rect 0 (3 * (n : Int)) 0 n


noncomputable def fkRectDevelopedThreeByOneVerticalEndpointPairs (n : Nat) :
    Finset ((fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) := by
  classical
  letI : Fintype (fkRectDevelopedThreeByOneRect n) := by
    rw [fkRectDevelopedThreeByOneRect]
    exact (rect_finite 0 (3 * (n : Int)) 0 n).fintype
  exact Finset.univ.filter fun p => p.1.1 1 = 0 ∧ p.2.1 1 = n

end
end StatMech.FrontierD
