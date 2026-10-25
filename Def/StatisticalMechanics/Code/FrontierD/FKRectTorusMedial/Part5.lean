/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part2


namespace StatMech.FrontierD

def fkRectTorusGraph (R : FKRectTorus) : SimpleGraph R.Vertex where
  Adj x y := ∃ a : R.EdgeIndex, fkRectTorusIndexedEdge R a = s(x, y)
  symm := by
    constructor
    rintro x y ⟨a, ha⟩
    exact ⟨a, by simpa [Sym2.eq_swap] using ha⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, ha⟩ := h
    exact fkRectTorusIndexedEdge_ne_diag R a x ha⟩


def fkRectOpenGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex where
  Adj x y := ∃ a : R.EdgeIndex,
    omega a = true ∧ fkRectTorusIndexedEdge R a = s(x, y)
  symm := by
    constructor
    rintro x y ⟨a, hopen, ha⟩
    exact ⟨a, hopen, by simpa [Sym2.eq_swap] using ha⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, _, ha⟩ := h
    exact fkRectTorusIndexedEdge_ne_diag R a x ha⟩

end StatMech.FrontierD
