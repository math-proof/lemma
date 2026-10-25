/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


def bcv_ClusterTreeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (H T : SimpleGraph (↑S : Type)) (_ : DecidableRel T.Adj) (ιU : Site 2 → (↑S : Type)),
    T ≤ H ∧ T.IsTree ∧ (∀ v, 1 ≤ T.degree v) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y →
      ∃ v₁ v₂ v₃ : (↑S : Type),
        v₁ ≠ ιU y ∧ v₂ ≠ ιU y ∧ v₃ ≠ ιU y ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₁ v₂ ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₁ v₃ ∧
        ¬ (bkg_deleteVertex H (ιU y)).Reachable v₂ v₃) ∧
    (∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box 2 R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    (∀ v : (↑S : Type), T.degree v = 1 → (v : Site 2) ∈ vertexBoundary 2 R)


end StatMech.Walls
