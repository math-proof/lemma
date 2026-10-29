/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsgspantreegn
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
import Def.StatisticalMechanics.Code.Walls.bfinfinalclose
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


theorem bfin_bk_of_globalArmForest (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bfin_GlobalArmForest ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bfin_bk_of_subforestData p hp1 hp0 hdata


theorem bfin_status :
    
    (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsAcyclic → G ≤ T → G.IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), 1 ≤ R →
      (∀ y, y ∈ box 2 R → ¬ bc67_IsGnTrifurcation ω L y) → bau_ArmSubforestData ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hdata; exact bfin_bk_of_subforestData p hp1 hp0 hdata
  · intro V T G hT hle; exact bfin_acyclic_free hT hle
  · intro ω L R hR hno; exact bfin_datum_of_noTrif ω L R hR hno
  · intro ω L R h; exact bfin_datum_implies_count ω L R h

end StatMech.Walls
