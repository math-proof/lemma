/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InfiniteFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy
open MeasureTheory Set Filter Topology SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace FK

open StatMech.Lattice ConfigSpace

variable {d : ℕ}


noncomputable def innerEdgeLEEmbedding (d : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    Sym2 (boxVerts d N) ↪ Sym2 (boxVerts d M) where
  toFun := innerEdgeLE d hNM
  inj' := dfi_innerEdgeLE_injective d hNM


noncomputable def liftPatternFinset (d : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) : Finset (Sym2 (boxVerts d M)) :=
  I.map (innerEdgeLEEmbedding d hNM)


noncomputable def liftPatternConfig (d : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I) :
    ConfigSpace ↥(liftPatternFinset d hNM I) := fun x =>
  eta ⟨Classical.choose (Finset.mem_map.mp x.2),
    (Classical.choose_spec (Finset.mem_map.mp x.2)).1⟩

end FK
end StatMech
