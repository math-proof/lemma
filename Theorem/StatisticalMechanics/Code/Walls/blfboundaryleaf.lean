/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/blfboundaryleaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
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


theorem blf_leaf_of_interiorDeg2 {V : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {B : V → Prop}
    (h2 : ∀ v, ¬ B v → 2 ≤ F.degree v) :
    ∀ v, F.degree v = 1 → B v := by
  intro v hv
  by_contra hB
  have := h2 v hB
  omega


theorem blf_bc69_of_interiorDeg2 {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (S : Set (Site d)) (hSfin : Fintype (↑S : Type)) (hSne : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (hGdec : DecidableRel G.Adj) (ιU : Site d → (↑S : Type))
    (hac : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hint : ∀ v : (↑S : Type), ((v : Site d) ∉ vertexBoundary d R) → 2 ≤ G.degree v) :
    bc69_Gn_globalForest ω L R := by
  refine ⟨S, hSfin, hSne, G, hGdec, ιU, hac, hmin, hdeg3, hinj, ?_⟩
  intro v hv
  by_contra hvb
  have := hint v hvb
  omega


end StatMech.Walls
