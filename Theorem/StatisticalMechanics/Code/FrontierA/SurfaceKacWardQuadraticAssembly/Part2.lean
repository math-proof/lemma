/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


theorem kwGraphFormalRoot_coeff_surfaceQuadratic
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (kwGraphFormalRoot G phase) =
      (surfaceParitySign
        (surfaceBaseQuadraticParity
          (surfaceSubgraphHomology edgeClass S)) : Complex) := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hcoeff⟩ :=
    kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
      G phase (surfaceBaseCycleCoefficient edgeClass) hlog hdeg S hS
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
      (0 : SurfaceSpinStructure g) Finset.univ homology hpair
  have hhomology : surfaceSubgraphHomology edgeClass S = ∑ i, homology i := by
    exact surfaceSubgraphHomology_biUnion edgeClass S
      (fun i => (cycle i).edges.toFinset) hcover hedgeDisjoint
  unfold surfaceBaseCycleCoefficient homology at *
  simpa only [surfaceQuadraticParity_zero, hhomology] using hsign.symm


theorem kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (S : Finset (Sym2 V)) (hS : S ∉ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) = 0 := by
  classical
  unfold kwGraphFormalRoot
  rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro f hf
  by_contra hprod
  apply hS
  let support : Nat -> Finset (Sym2 V) := fun i => (f i).support
  have hpiece : ∀ i ∈ Finset.range n,
      support i ∈ evenSubgraphs G := by
    intro i hi
    have hcoeffNe : MvPowerSeries.coeff (f i)
        (kwGraphFormalLog G phase) ≠ 0 := by
      intro hzero
      apply hprod
      exact Finset.prod_eq_zero hi hzero
    have hcomponent :=
      ons_finsuppAntidiag_finsetExponent_component
        (Finset.range n) S f hf hi
    change kwGraphFormalLogCoeff G phase (f i) ≠ 0 at hcoeffNe
    rw [hcomponent] at hcoeffNe
    obtain ⟨root, q, hq, hqedges⟩ := hlog.2 (support i) hcoeffNe
    rw [← hqedges]
    exact ons_cycle_edges_evenSubgraph G q hq
  have hpair : ((Finset.range n : Finset Nat) : Set Nat).PairwiseDisjoint
      support := by
    intro i hi j hj hij
    exact ons_finsuppAntidiag_finsetExponent_support_disjoint
      (Finset.range n) S f hf hi hj hij
  have hunion := ons_evenSubgraphs_biUnion_of_pairwiseDisjoint
    G (Finset.range n) support hpair hpiece
  rw [← ons_finsuppAntidiag_finsetExponent_support_cover
    (Finset.range n) S f hf] at hunion
  exact hunion


end StatMech.FrontierA
