/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def jei_pushGraph (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    SimpleGraph (Site 2) where
  Adj a b := ∃ x y : P.V, K.Adj x y ∧ P.emb x = a ∧ P.emb y = b
  symm := by constructor; rintro a b ⟨x, y, hadj, rfl, rfl⟩; exact ⟨y, x, hadj.symm, rfl, rfl⟩
  loopless := ⟨by
    rintro a ⟨x, y, hadj, hx, hy⟩
    have : x = y := P.emb.injective (hx.trans hy.symm)
    exact K.irrefl (this ▸ hadj)⟩

end Lattice
end StatMech
