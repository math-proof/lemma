/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

open FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem localizedGraph_edgeFinset (T : Finset V)
    [DecidableRel (localizedGraph G T).Adj] :
    (localizedGraph G T).edgeFinset = edgesIn G T := by
  classical
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  unfold localizedGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact fun h => h.1
  · intro he
    exact ⟨he, G.not_isDiag_of_mem_edgeFinset (Finset.mem_filter.mp he).1⟩

set_option maxHeartbeats 1000000 in


theorem expectationJ_couplingIn_one_eq_induced (beta : ℝ) (T : Finset V)
    {o x : V} (ho : o ∈ T) (hx : x ∈ T) :
    expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} =
      Ising.isingExpectation
        (G.comap (Subtype.val : {v // v ∈ T} → V)) beta 0
        (Ising.spinProd {⟨o, ho⟩, ⟨x, hx⟩}) := by
  classical
  let P : V → Prop := fun v => v ∈ T
  let L : SimpleGraph {v // P v} := FK.agl_left G P
  let I : SimpleGraph {v // ¬ P v} := ⊥
  let S : SimpleGraph ({v // P v} ⊕ {v // ¬ P v}) := L ⊕g I
  let K : SimpleGraph V := localizedGraph G T
  let A : Finset {v // P v} := {⟨o, ho⟩, ⟨x, hx⟩}
  let σ : ({v // P v} ⊕ {v // ¬ P v}) ≃ V := FK.agl_sumEquiv P
  letI : DecidableRel L.Adj := Classical.decRel _
  letI : DecidableRel I.Adj := Classical.decRel _
  letI : DecidableRel K.Adj := Classical.decRel _
  have hσ : ∀ a b, S.Adj a b ↔ K.Adj (σ a) (σ b) := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      intro hab heq
      exact G.ne_of_adj hab (congrArg Subtype.val heq)
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ hb => (b.property hb).elim
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ ha => (a.property ha).elim
    · simp [S, L, I, K, localizedGraph, σ, P, FK.agl_sumEquiv,
        SimpleGraph.fromEdgeSet_adj, edgesIn, edgeInside]
      exact fun _ ha _ => (a.property ha).elim
  have hmap :
      (A.map ⟨Sum.inl, Sum.inl_injective⟩).map σ.toEmbedding =
        ({o, x} : Finset V) := by
    ext z
    simp [A, σ, P, FK.agl_sumEquiv]
  have hK : K.edgeFinset = edgesIn G T := by
    simpa [K] using localizedGraph_edgeFinset G T
  calc
    expectationJ G beta (couplingIn (fun _ => 1) T) {o, x} =
        expJ (edgesIn G T) (fun _ => beta) (fun _ => 0)
          (Ising.spinProd {o, x}) := by
      simpa using expectationJ_couplingIn_eq_expJ G beta (fun _ => 1) T {o, x}
    _ = Ising.isingExpectation K beta 0 (Ising.spinProd {o, x}) := by
      rw [← hK]
      simpa using (Ising.isingExpectation_spinProd_eq_expJ K beta 0 {o, x}).symm
    _ = Ising.isingExpectation S beta 0
          (Ising.spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) := by
      rw [Ising.isingExpectation_spinProd_relabel S K σ hσ beta 0,
        hmap]
    _ = Ising.isingExpectation L beta 0 (Ising.spinProd A) :=
      by simpa [S] using Ising.isingExpectation_spinProd_sum_inl L I beta 0 A
    _ = Ising.isingExpectation
          (G.comap (Subtype.val : {v // v ∈ T} → V)) beta 0
          (Ising.spinProd {⟨o, ho⟩, ⟨x, hx⟩}) := by
      rfl


theorem hcaBondDelta_incident_eq (beta h : ℝ) (o y : V) (hoy : o ≠ y) :
    HcovAssembly.hcaBondDelta G beta h o s(o, y) =
      sourcePairDisconnSum (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) {some y, none} ∅ (some o) none := by
  unfold HcovAssembly.hcaBondDelta HcovAssembly.hcaBondSource
  congr 2
  ext z
  cases z <;> simp [Finset.mem_symmDiff, someEmb, hoy, eq_comm] <;> aesop


theorem hcaBondDelta_incident_bound (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (o y : V) (hoy : o ≠ y) :
    Ising.isingExpectation G beta h (Ising.spinProd {y}) *
        HcovAssembly.hcaBondDelta G beta h o s(o, y) ≥
      isingDeltaSelfLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some y) none := by
  have hJ : ∀ e : Sym2 (Option V),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({y} : Finset V) (by simp)
  have hsource : insert none (({y} : Finset V).map someEmb) =
      ({some y, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  rw [hcaBondDelta_incident_eq G beta h o y hoy, ← hdict]
  exact ising_delta_bound_cleared_self (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) hbeta hJ (by simp)


theorem hcaBondDelta_nonincident_eq_deltaPair_add (beta h : ℝ)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    HcovAssembly.hcaBondDelta G beta h o s(x, y) =
      isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none +
        isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some y) (some x) none := by
  have hsource : HcovAssembly.hcaBondSource o s(x, y) =
      ({some o, some x, some y, none} : Finset (Option V)) := by
    rw [HcovAssembly.hcaBondSource_mk]
    ext z
    cases z <;> simp [Finset.mem_symmDiff, someEmb, hox, hoy, hxy, eq_comm] <;> aesop
  rw [HcovAssembly.hcaBondDelta, hsource]
  exact sourcePairDisconn_eq_deltaPair_add (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1))
    (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp)


theorem isingDeltaPair_field_bound (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Ising.isingExpectation G beta h (Ising.spinProd {y}) *
        isingDeltaPairSum (withGhost G) beta
          (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none ≥
      isingDeltaLowerMass (withGhost G) beta
        (ghostCoupling h beta (fun _ => 1)) (some o) (some x) (some y) none := by
  have hJ : ∀ e : Sym2 (Option V),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hdict := fgd_expectationJ_ghost_eq_odd G beta h ({y} : Finset V) (by simp)
  have hsource : insert none (({y} : Finset V).map someEmb) =
      ({some y, none} : Finset (Option V)) := by
    ext z
    cases z <;> simp [someEmb]
  rw [hsource] at hdict
  rw [← hdict]
  exact ising_delta_bound_cleared (withGhost G) beta
    (ghostCoupling h beta (fun _ => 1)) hbeta hJ
    (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp)

end Sharpness
end StatMech
