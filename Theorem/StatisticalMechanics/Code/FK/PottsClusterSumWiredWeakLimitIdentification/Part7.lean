/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


theorem conditionalClusterColorPMF_apply
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (sigma : V -> Fin q) :
    conditionalClusterColorPMF G bdry b omega sigma =
      if h : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
        (Fintype.card (CompatibleBoundarySpin G bdry b omega) : ENNReal)⁻¹
      else 0 := by
  classical
  rw [conditionalClusterColorPMF, PMF.map_apply]
  by_cases h : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
  · rw [dif_pos h, tsum_eq_single (⟨sigma, h⟩ : CompatibleBoundarySpin G bdry b omega)]
    · simp
    · intro tau hne
      rw [if_neg]
      intro heq
      apply hne
      exact Subtype.ext heq.symm
  · rw [dif_neg h]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro tau htau
    rw [if_neg]
    intro heq
    apply h
    simpa [heq] using tau.2


theorem conditionalClusterColorPMF_eq_pinnedWiredComponents
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) :
    conditionalClusterColorPMF G bdry b omega =
      (PMF.uniformOfFintype
        {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b}).map
        (fun tau x => tau.1
          ((wiredSub G bdry omega).connectedComponentMk x)) := by
  let E := compatibleBoundarySpinEquivPinnedWiredComponents
    G bdry b omega v0 hv0
  have huniform :
      (PMF.uniformOfFintype
        {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b}).map E.symm =
        PMF.uniformOfFintype (CompatibleBoundarySpin G bdry b omega) :=
    uniformOfFintype_map_equiv E.symm
  rw [conditionalClusterColorPMF, ← huniform, PMF.map_comp]
  congr 1

set_option maxHeartbeats 3000000 in


theorem extendWiredClusterSumSpin_law
    {d n q : Nat} [NeZero q] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (v0 : boxVerts d n) (hv0 : boxBoundary d n v0) :
    Measure.map (fun label (x : boxVerts d n) =>
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (x : Site d))
      (pottsIIDLabelMeasure d q) =
        (conditionalClusterColorPMF (boxGraph d n) (boxBoundary d n)
          boundaryColor omega).toMeasure := by
  let W := wiredSub (boxGraph d n) (boxBoundary d n) omega
  let c0 := W.connectedComponentMk v0
  let K := {C : W.ConnectedComponent // C ≠ c0}
  let r : K -> Site d := fun C => (C.1.out : boxVerts d n)
  let repColor : (Site d -> Fin q) -> K -> Fin q := fun label C =>
    pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega) label (r C)
  let E : (K -> Fin q) ≃ CompatibleBoundarySpin
      (boxGraph d n) (boxBoundary d n) boundaryColor omega :=
    nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin
      (boxGraph d n) (boxBoundary d n) boundaryColor omega v0 hv0
  have hrep := extendWiredNonboundaryRepresentatives_law
    hd hn boundaryColor omega v0 hv0
  change Measure.map repColor (pottsIIDLabelMeasure d q) =
      Measure.infinitePi fun _ : K =>
        (PMF.uniformOfFintype (Fin q)).toMeasure at hrep
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform] at hrep
  have hfactor : (fun label (x : boxVerts d n) =>
      pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
        label (x : Site d)) = Subtype.val ∘ E ∘ repColor := by
    funext label x
    rw [Function.comp_apply, Function.comp_apply]
    rw [nonboundaryWiredComponentColorsEquivCompatibleBoundarySpin_apply]
    by_cases hx : W.connectedComponentMk x = c0
    · rw [dif_pos hx]
      have hconn : ConnToBdry (boxGraph d n) (boxBoundary d n) omega x :=
        (connToBdry_iff_componentMk_eq
          (boxGraph d n) (boxBoundary d n) v0 hv0 omega x).mpr hx
      exact pottsClusterSumSpin_of_infinite boundaryColor
        (extendWiredEdge d n omega) label (x : Site d)
        (cluster_extendWiredEdge_infinite_of_connToBdry hd hn omega x hconn)
    · rw [dif_neg hx]
      let C : K := ⟨W.connectedComponentMk x, hx⟩
      change pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (x : Site d) =
        pottsClusterSumSpin boundaryColor (extendWiredEdge d n omega)
          label (r C)
      apply pottsClusterSumSpin_eq_of_connected boundaryColor
      apply wiredSub_reachable_connected_extendWiredEdge hd hn omega
      apply SimpleGraph.ConnectedComponent.exact
      change W.connectedComponentMk x = W.connectedComponentMk C.1.out
      exact (Quot.out_eq C.1).symm
  have hrepMeas : Measurable repColor := by
    exact measurable_pi_lambda _ fun C =>
      (measurable_pottsClusterSumSpin_apply boundaryColor (r C)).comp
        (measurable_const.prodMk measurable_id)
  have hpostMeas : Measurable (Subtype.val ∘ E) := Measurable.of_discrete
  rw [hfactor]
  have hcomp : Subtype.val ∘ E ∘ repColor =
      (Subtype.val ∘ E) ∘ repColor := rfl
  rw [hcomp, ← Measure.map_map hpostMeas hrepMeas, hrep]
  let uniformK := PMF.uniformOfFintype (K -> Fin q)
  have huniformE : uniformK.map E =
      PMF.uniformOfFintype
        (CompatibleBoundarySpin (boxGraph d n) (boxBoundary d n)
          boundaryColor omega) :=
    uniformOfFintype_map_equiv E
  have hpmf : uniformK.map (Subtype.val ∘ E) =
      conditionalClusterColorPMF (boxGraph d n) (boxBoundary d n)
        boundaryColor omega := by
    rw [← PMF.map_comp, huniformE]
    rfl
  change Measure.map (Subtype.val ∘ E) uniformK.toMeasure = _
  rw [PMF.toMeasure_map (Subtype.val ∘ E) uniformK Measurable.of_discrete,
    hpmf]

theorem compatibleBoundarySpin_card_pos
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V)) :
    0 < Fintype.card (CompatibleBoundarySpin G bdry b omega) := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨fun _ => b, by
    constructor
    · intro x y hxy
      rfl
    · intro x hx
      rfl⟩⟩


theorem ivp_wiredJointProb_eq_wiredFkProb_div_card
    {q : Nat} [NeZero q] (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0)
    (sigma : V -> Fin q) (omega : ConfigSpace (Sym2 V)) :
    ivp_wiredJointProb G bdry b beta J (sigma, omega) =
      if ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
        wiredFkProb G bdry (1 - Real.exp (-(beta * J))) (q : Real) omega /
          Fintype.card (CompatibleBoundarySpin G bdry b omega)
      else 0 := by
  classical
  let C : Nat := Fintype.card (CompatibleBoundarySpin G bdry b omega)
  have hC : (C : Real) ≠ 0 := by
    exact_mod_cast (compatibleBoundarySpin_card_pos G bdry b omega).ne'
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_neZero q
  have hcount : ∀ eta : ConfigSpace (Sym2 V),
      1 ≤ numClustersBC G (boundaryCliqueGraph bdry) eta :=
    fun eta => one_le_numClustersBC G bdry v0 eta
  have hfk : wiredFkProb G bdry (1 - Real.exp (-(beta * J))) (q : Real) omega =
      edgeProduct G (1 - Real.exp (-(beta * J))) omega * C /
        esZWired G bdry q b (1 - Real.exp (-(beta * J))) := by
    rw [wiredFkProb_eq_bcProb]
    rw [← esWiredSecondMarginal_eq_bcProb G bdry b
      (1 - Real.exp (-(beta * J))) omega v0 hv0 (Nat.pos_of_neZero q) hcount]
    unfold esWiredSecondMarginal
    rw [esWeightWired_sum_spins]
    simp only [C, CompatibleBoundarySpin, Fintype.card_subtype]
  by_cases hcompat : ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma
  · rw [if_pos hcompat, ivp_wiredJointProb, esWeightWired,
      if_pos hcompat.2, esWeight_eq_of_compatible]
    rw [if_pos ((compatible_iff_constOnOpen G sigma omega).mpr hcompat.1), hfk]
    change edgeProduct G (1 - Real.exp (-(beta * J))) omega /
        esZWired G bdry q b (1 - Real.exp (-(beta * J))) =
      (edgeProduct G (1 - Real.exp (-(beta * J))) omega * (C : Real) /
        esZWired G bdry q b (1 - Real.exp (-(beta * J)))) / (C : Real)
    field_simp
  · rw [if_neg hcompat, ivp_wiredJointProb, esWeightWired]
    by_cases hbf : BoundaryFixed bdry b sigma
    · rw [if_pos hbf, esWeight_eq_of_compatible]
      rw [if_neg (by
        intro hc
        exact hcompat ⟨(compatible_iff_constOnOpen G sigma omega).mp hc, hbf⟩)]
      simp
    · simp [hbf]


end Wired
end StatMech.FK
