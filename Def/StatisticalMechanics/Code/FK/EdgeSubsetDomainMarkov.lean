/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def edgeSubsetFrozenExteriorGraph
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := (H.Adj x y ∧ ¬K.Adj x y ∧ psi s(x, y) = true) ∨ B.Adj x y
  symm := by
    constructor
    rintro x y (hxy | hxy)
    · exact Or.inl ⟨hxy.1.symm, fun hyx => hxy.2.1 hyx.symm,
        by simpa [Sym2.eq_swap] using hxy.2.2⟩
    · exact Or.inr hxy.symm
  loopless := ⟨by
    rintro x (hxx | hxx)
    · exact (H.ne_of_adj hxx.1) rfl
    · exact (B.ne_of_adj hxx) rfl⟩

end
end StatMech.FK
