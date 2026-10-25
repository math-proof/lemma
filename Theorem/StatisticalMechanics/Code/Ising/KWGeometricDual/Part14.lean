/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part15
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_walkParity_copy {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : Finset (Sym2 V)} {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') :
    walkParity G D (p.copy hu hv) = walkParity G D p := by
  subst u'
  subst v'
  rfl


theorem kwg_componentParityColour_adj_xor {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {D : Finset (Sym2 V)} (hev : EvenOnCycles G D)
    {x y : V} (hxy : G.Adj x y) :
    (kwg_componentParityColour G D x).xor (kwg_componentParityColour G D y) =
      decide (s(x, y) ∈ D) := by
  classical
  have hC : G.connectedComponentMk x = G.connectedComponentMk y :=
    ConnectedComponent.sound hxy.reachable
  let px := kwg_componentPath G x
  let py := kwg_componentPath G y
  let qxy : G.Walk x y := SimpleGraph.Walk.cons hxy (.nil : G.Walk y y)
  have hroots : (G.connectedComponentMk x).out = (G.connectedComponentMk y).out :=
    congrArg Quot.out hC
  let py' : G.Walk (G.connectedComponentMk x).out y := py.copy hroots.symm rfl
  let via : G.Walk (G.connectedComponentMk x).out y := px.append qxy
  have hpar : walkParity G D py' = walkParity G D via :=
    walkParity_eq_of_evenOnCycles hev py' via
  have hpy : walkParity G D py' = kwg_componentParityColour G D y := by
    change walkParity G D (py.copy hroots.symm rfl) = walkParity G D py
    exact kwg_walkParity_copy py hroots.symm rfl
  have hvia : walkParity G D via =
      (kwg_componentParityColour G D x).xor (decide (s(x, y) ∈ D)) := by
    rw [walkParity_append, walkParity_singleton]
    rfl
  rw [hpy, hvia] at hpar
  rw [hpar]
  cases kwg_componentParityColour G D x <;>
    cases decide (s(x, y) ∈ D) <;> rfl


theorem kwg_exists_colour_of_evenOnCycles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {D : Finset (Sym2 V)}
    (hsub : D ⊆ G.edgeFinset) (hev : EvenOnCycles G D) :
    ∃ c : V → Bool, cutEdges G c = D := by
  classical
  let c := kwg_componentParityColour G D
  refine ⟨c, ?_⟩
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : G.Adj x y
      · rw [mem_cutEdges_iff G c hxy]
        have hx := kwg_componentParityColour_adj_xor hev hxy
        by_cases hm : s(x, y) ∈ D
        · rw [decide_eq_true hm] at hx
          constructor
          · exact fun _ => hm
          · intro _
            cases hc1 : c x <;> cases hc2 : c y <;> simp_all [c]
        · rw [decide_eq_false hm] at hx
          constructor
          · intro hne
            cases hc1 : c x <;> cases hc2 : c y <;> simp_all [c]
          · exact fun h => (hm h).elim
      · have hD : s(x, y) ∉ D := by
          intro hm
          have := hsub hm
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
          exact hxy this
        have hdis : s(x, y) ∉ cutEdges G c := by
          intro hm
          have := (Finset.filter_subset _ _) hm
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
          exact hxy this
        simp [hD, hdis]


theorem kwg_dualEven_exists_primalCut (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (hev : kwg_IsEven (kwg_dualEnds P) F) :
    ∃ c : ConfigSpace P.V, kwg_cutSet (kwg_primalEnds P) c = F := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  have hsub : kwg_primalEdgeFinset P F ⊆ P.G.edgeFinset := by
    intro e he
    rw [kwg_primalEdgeFinset, Finset.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact f.2
  obtain ⟨c, hc⟩ := kwg_exists_colour_of_evenOnCycles hsub
    (kwg_dualEven_evenOnCycles P F hev)
  refine ⟨c, ?_⟩
  apply Finset.ext
  intro e
  simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : P.G.Adj x y := (SimpleGraph.mem_edgeSet P.G).mp he
      change c x ≠ c y ↔ ⟨s(x, y), he⟩ ∈ F
      rw [← mem_cutEdges_iff P.G c hxy, hc]
      exact kwg_mem_primalEdgeFinset P F ⟨s(x, y), he⟩


theorem kwg_componentIncident_isEven (P : PlanarZ2Subgraph) (C : kwg_Face P) : by
    classical
    letI : Fintype P.V := Fintype.ofFinite P.V
    letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
    exact kwg_IsEven (kwg_primalEnds P)
      ((kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  intro x
  have hcard :
      (((kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))).filter
          (fun e => kwg_incidentMod2 x (kwg_primalEnds P e))).card =
        ((kwg_componentBoundaryGraph P C).incidenceFinset x).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      rw [Finset.mem_filter] at he
      have hcut := (kwg_incident_iff_componentCut P e C).mp
        (Finset.mem_filter.mp he.1).2
      have hedge : e.1 ∈ (kwg_componentBoundaryGraph P C).edgeSet := by
        rcases e with ⟨e, hedge⟩
        induction e using Sym2.inductionOn with
        | _ u v =>
            rw [SimpleGraph.mem_edgeSet]
            exact ⟨(SimpleGraph.mem_edgeSet P.G).mp hedge, hcut⟩
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset]
      exact ⟨hedge, (kwg_primal_incident_iff_mem P e x).mp he.2⟩
    · intro e _ f _ hef
      exact Subtype.ext hef
    · intro g hg
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset] at hg
      have hdata : g ∈ P.G.edgeSet ∧
          Sym2.map P.emb g ∈ jed_cutSet (fun z =>
            (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) := by
        induction g using Sym2.inductionOn with
        | _ u v =>
            have hb := (SimpleGraph.mem_edgeSet
              (kwg_componentBoundaryGraph P C)).mp hg.1
            exact ⟨(SimpleGraph.mem_edgeSet P.G).mpr hb.1, hb.2⟩
      let e : kwg_Edge P := ⟨g, hdata.1⟩
      refine ⟨e, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, (kwg_primal_incident_iff_mem P e x).mpr hg.2⟩
      rw [Finset.mem_filter]
      exact ⟨kwg_mem_allEdges P e, (kwg_incident_iff_componentCut P e C).mpr hdata.2⟩
  rw [hcard, SimpleGraph.card_incidenceFinset_eq_degree]
  exact kwg_componentBoundaryGraph_even P C x


theorem kwg_primalCut_isEven (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    kwg_IsEven (kwg_dualEnds P) (kwg_cutSet (kwg_primalEnds P) c) := by
  classical
  intro C
  let B : Finset (kwg_Edge P) :=
    (kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))
  have hs := kwg_even_split_card (kwg_primalEnds P) B c
    (kwg_componentIncident_isEven P C)
  have heq :
      (kwg_cutSet (kwg_primalEnds P) c).filter
          (fun e => kwg_incidentMod2 C (kwg_dualEnds P e)) =
        B.filter (fun e => kwg_isSplit c (kwg_primalEnds P e)) := by
    ext e
    simp only [B, kwg_cutSet, Finset.mem_filter, Finset.mem_univ, kwg_mem_allEdges, true_and]
    tauto
  change Even ((kwg_cutSet (kwg_primalEnds P) c).filter
    (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))).card
  rw [heq]
  exact hs


theorem kwg_sum_prod_bond {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) :
    (∑ c : ConfigSpace V, ∏ e ∈ F, bond c (ends e)) =
      if kwg_IsEven ends F then (2 : ℝ) ^ Fintype.card V else 0 := by
  classical
  have hstep : ∀ c : ConfigSpace V,
      (∏ e ∈ F, bond c (ends e)) =
        ∏ v ∈ Finset.univ.filter (fun v => ¬ Even (kwg_degree ends F v)), spin c v := by
    intro c
    rw [kwg_prod_bond_eq_prod_pow_degree ends c F]
    simp_rw [spin_pow c]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    by_cases h : Even (kwg_degree ends F v) <;> simp [h]
  simp_rw [hstep]
  rw [sum_prod_spin_set]
  by_cases hev : kwg_IsEven ends F
  · rw [if_pos hev, if_pos]
    rw [Finset.filter_eq_empty_iff]
    intro v _
    exact not_not_intro ((kwg_IsEven_iff_degree ends F).mp hev v)
  · rw [if_neg hev, if_neg]
    rw [kwg_IsEven_iff_degree, not_forall] at hev
    obtain ⟨v, hv⟩ := hev
    exact Finset.ne_empty_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)


theorem kwg_isingZ_high_temp {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (ends : E → Sym2 V) (β : ℝ) :
    kwg_isingZ ends β =
      (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ Fintype.card E *
        ∑ F : Finset E, if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0 := by
  classical
  unfold kwg_isingZ
  have hweight : ∀ c : ConfigSpace V,
      Real.exp (β * ∑ e : E, bond c (ends e)) =
        (Real.cosh β) ^ Fintype.card E *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) := by
    intro c
    rw [Finset.mul_sum, Real.exp_sum]
    calc
      (∏ e : E, Real.exp (β * bond c (ends e))) =
          ∏ e : E, (Real.cosh β * (1 + Real.tanh β * bond c (ends e))) := by
            apply Finset.prod_congr rfl
            intro e _
            exact exp_mul_eq_cosh_mul β (bond c (ends e))
              (bond_eq_one_or_neg_one c (ends e))
      _ = (∏ _e : E, Real.cosh β) *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) :=
            (Finset.prod_mul_distrib (s := (Finset.univ : Finset E))
              (f := fun _e => Real.cosh β)
              (g := fun e => 1 + Real.tanh β * bond c (ends e)))
      _ = (Real.cosh β) ^ Fintype.card E *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) := by
            rw [Finset.prod_const, Finset.card_univ]
  simp_rw [hweight]
  have hexpand : ∀ c : ConfigSpace V,
      (∏ e : E, (1 + Real.tanh β * bond c (ends e))) =
        ∑ F : Finset E, ∏ e ∈ F, (Real.tanh β * bond c (ends e)) := by
    intro c
    simpa using Finset.prod_one_add (s := (Finset.univ : Finset E))
      (f := fun e => Real.tanh β * bond c (ends e))
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ Fintype.card E *
      ∑ F : Finset E, (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0) =
    (Real.cosh β) ^ Fintype.card E *
      ((2 : ℝ) ^ Fintype.card V *
        ∑ F : Finset E, (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0)) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  have hpull : ∀ c : ConfigSpace V,
      (∏ e ∈ F, (Real.tanh β * bond c (ends e))) =
        (Real.tanh β) ^ F.card * ∏ e ∈ F, bond c (ends e) := by
    intro c
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hsum := kwg_sum_prod_bond ends F
  calc
    (Real.tanh β) ^ F.card * (∑ c : ConfigSpace V, ∏ e ∈ F, bond c (ends e)) =
        (Real.tanh β) ^ F.card *
          (if kwg_IsEven ends F then (2 : ℝ) ^ Fintype.card V else 0) :=
      congrArg (fun z => (Real.tanh β) ^ F.card * z) hsum
    _ = (2 : ℝ) ^ Fintype.card V *
        (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0) := by
      by_cases hev : kwg_IsEven ends F <;> simp [hev, mul_comm]


end Ising
end StatMech
