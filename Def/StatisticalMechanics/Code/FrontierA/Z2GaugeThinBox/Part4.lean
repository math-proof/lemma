/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part4
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

def thinBoxSurfaceEquiv (n : ℕ) :
    {A : Finset (thinBoxPlaquette n) //
        A ∈ gaugeClosedSurfaceFamily (thinBoxIncidence n)} ≃
      {delta : Finset (Sym2 (Fin (n + 1))) //
        delta ∈ cutSpace (thinBoxDualGraph n)} where
  toFun A := ⟨A.1.map (dualPlaquetteEmbedding (thinBoxDualEdge n)), by
    rw [cutSpace_eq_edgePowerset_of_isTree _ (thinBoxDualGraph_isTree n),
      Finset.mem_powerset]
    intro e he
    rw [Finset.mem_map] at he
    obtain ⟨p, _, rfl⟩ := he
    exact (thinBoxDualEdge n p).2⟩
  invFun delta := ⟨thinBoxPlaquettePreimage n delta.1, by
    rw [gaugeClosedSurfaceFamily, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), thinBox_isClosed n _⟩⟩
  left_inv A := by
    apply Subtype.ext
    ext p
    rw [mem_thinBoxPlaquettePreimage, Finset.mem_map]
    constructor
    · rintro ⟨q, hq, hqp⟩
      have hedge : thinBoxDualEdge n q = thinBoxDualEdge n p := by
        apply Subtype.ext
        exact hqp
      have hpq : q = p := (thinBoxDualEdge n).injective hedge
      simpa [hpq] using hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  right_inv delta := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      rw [Finset.mem_map] at he
      obtain ⟨p, hp, rfl⟩ := he
      exact (mem_thinBoxPlaquettePreimage n delta.1 p).mp hp
    · intro he
      have hsubset : delta.1 ⊆ (thinBoxDualGraph n).edgeFinset := by
        have hpow : delta.1 ∈ (thinBoxDualGraph n).edgeFinset.powerset := by
          rw [← cutSpace_eq_edgePowerset_of_isTree _ (thinBoxDualGraph_isTree n)]
          exact delta.2
        exact Finset.mem_powerset.mp hpow
      let p := (thinBoxDualEdge n).symm ⟨e, hsubset he⟩
      rw [Finset.mem_map]
      refine ⟨p, (mem_thinBoxPlaquettePreimage n delta.1 p).mpr ?_, ?_⟩
      · simpa [p]
      · change (thinBoxDualEdge n p).1 = e
        simp [p]

end
end StatMech.FrontierA
