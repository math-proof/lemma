/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DecayOfCorrelations
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.BoundaryInfluenceDecay
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem fbd_wired_density_eq_of_offCentreCarrier (N : ℕ) (v : Site d)
    (eb eb' : Sym2 (boxVerts d N)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcarrier : Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0))
    (htrans : ∀ k,
        edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb'))
          = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  
  have hC' := dfi_wired_density_eq_limit N eb' hp hp1
  
  have hC := dfi_wired_density_eq_limit N eb hp hp1
  
  have hT : Tendsto (fun k =>
      edgeMargProb
          (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
          (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
    refine hC.congr (fun k => (htrans k).symm)
  
  
  have hdiff : Tendsto (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb')
        - edgeMargProb
            (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2)
            (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')))
      atTop (𝓝 0) := hcarrier
  
  have hsum := hdiff.add hT
  simp only [zero_add] at hsum
  have hcong : Tendsto (fun k =>
      edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb'))
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
    refine hsum.congr (fun k => ?_)
    ring
  exact (tendsto_nhds_unique hC' hcong).symm

end FK
end StatMech
