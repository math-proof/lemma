/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgctrifgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgfacyclicstep
import Theorem.StatisticalMechanics.Code.Walls.bc70globalforest.Part4
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
import Theorem.StatisticalMechanics.Code.Walls.bgctrifgraph
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

variable {d : ℕ}


def bgc_TrifForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site d → (↑S : Type)),
    
    (∀ t a b : (↑S : Type), G.Adj t a → G.Adj t b → a ≠ b →
      ¬ (bc67_contractedLattice ω L (t : Site d)).Reachable (a : Site d) (b : Site d)) ∧
    
    (∀ t a b : (↑S : Type), G.Adj a b → t ≠ a → t ≠ b →
      (bc67_contractedLattice ω L (t : Site d)).Reachable (a : Site d) (b : Site d)) ∧
    
    (∀ v, 1 ≤ G.degree v) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    
    (∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R)


end StatMech.Walls
