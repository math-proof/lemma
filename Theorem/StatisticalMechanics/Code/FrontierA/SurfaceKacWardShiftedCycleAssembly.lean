/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

theorem kwGraphFormalRoot_coeff_surfaceQuadratic_shifted
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (kwGraphFormalRoot G phase) =
      (surfaceParitySign
        (surfaceQuadraticParity lambda
          (surfaceSubgraphHomology edgeClass S)) : Complex) := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hcoeff⟩ :=
    kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
      G phase (surfaceSpinCycleCoefficient edgeClass lambda)
        hlog hdeg S hS
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  rw [hcoeff]
  let homology : I -> SurfaceHomology g := fun i =>
    surfaceSubgraphHomology edgeClass (cycle i).edges.toFinset
  have hpair : ∀ i ∈ (Finset.univ : Finset I),
      ∀ j ∈ (Finset.univ : Finset I), i ≠ j ->
        surfaceIntersection (homology i) (homology j) = 0 := by
    intro i hi j hj hij
    exact hisotropic (cycle i) (cycle j) (hcycle i) (hcycle j)
      (hvertDisjoint hi hj hij)
  have hsign :=
    surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero
      lambda Finset.univ homology hpair
  have hhomology : surfaceSubgraphHomology edgeClass S = ∑ i, homology i := by
    exact surfaceSubgraphHomology_biUnion edgeClass S
      (fun i => (cycle i).edges.toFinset) hcover hedgeDisjoint
  unfold surfaceSpinCycleCoefficient homology at *
  simpa only [hhomology] using hsign.symm

end StatMech.FrontierA
