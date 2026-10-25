/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectClosedWindingSubgroup_iff
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (u : Int × Int) :
    u ∈ fkRectClosedWindingSubgroup R omega x ↔
      ∃ p : (fkRectOpenGraph R omega).Walk x x,
        fkRectWalkWinding R p = u :=
  Iff.rfl


theorem fkRectClosedWindingSubgroup_eq_of_reachable
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Reachable x y) :
    fkRectClosedWindingSubgroup R omega x =
      fkRectClosedWindingSubgroup R omega y := by
  obtain ⟨r⟩ := hxy
  apply le_antisymm
  · rintro u ⟨p, hp⟩
    refine ⟨(r.reverse.append p).append r.reverse.reverse, ?_⟩
    rw [fkRectWalkWinding_conjugate]
    exact hp
  · rintro u ⟨q, hq⟩
    refine ⟨(r.append q).append r.reverse, ?_⟩
    rw [fkRectWalkWinding_conjugate]
    exact hq


end
end StatMech.FrontierD
