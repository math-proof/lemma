/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectClosedWindingSubgroup (R : FKRectTorus)
    (omega : R.Configuration) (x : R.Vertex) : AddSubgroup (Int × Int) where
  carrier := {u | ∃ p : (fkRectOpenGraph R omega).Walk x x,
    fkRectWalkWinding R p = u}
  zero_mem' := ⟨.nil, rfl⟩
  add_mem' := by
    rintro u v ⟨p, rfl⟩ ⟨q, rfl⟩
    refine ⟨p.append q, ?_⟩
    simpa using fkRectWalkWinding_append R p q
  neg_mem' := by
    rintro u ⟨p, rfl⟩
    refine ⟨p.reverse, ?_⟩
    simpa using fkRectWalkWinding_reverse R p

end
end StatMech.FrontierD
