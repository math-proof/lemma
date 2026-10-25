/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


theorem kwWeightedCycleComponentSeries_coeff
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex) (m : Sym2 V →₀ Nat) :
    MvPowerSeries.coeff m
        (kwWeightedCycleComponentSeries base cycle coefficient) =
      ∑ i : I, if ons_finsetExponent (cycle i).edges.toFinset = m then
        coefficient i else 0 := by
  classical
  unfold kwWeightedCycleComponentSeries
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPowerSeries.coeff_monomial]
  by_cases heq : ons_finsetExponent (cycle i).edges.toFinset = m
  · rw [if_pos heq.symm, if_pos heq]
  · rw [if_neg (Ne.symm heq), if_neg heq]

theorem kwWeightedCycleComponentSeries_coeff_piece
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) (j : I) :
    MvPowerSeries.coeff
        (ons_finsetExponent (cycle j).edges.toFinset)
        (kwWeightedCycleComponentSeries base cycle coefficient) =
      coefficient j := by
  classical
  rw [kwWeightedCycleComponentSeries_coeff, Fintype.sum_eq_single j]
  · simp
  · intro i hij
    rw [if_neg]
    intro heq
    apply hij
    apply ons_cycle_decomposition_edgeSet_injective base cycle hcycle hdisj
    exact ons_finsetExponent_injective heq

theorem kwWeightedCycleComponentSeries_hasSubst
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle) :
    PowerSeries.HasSubst
      (kwWeightedCycleComponentSeries base cycle coefficient) := by
  classical
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff,
    kwWeightedCycleComponentSeries_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro heq
  apply (ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)).ne_empty
  apply ons_finsetExponent_injective
  simpa [ons_finsetExponent] using heq


theorem kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag
    {V I : Type u} {K : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [DecidableEq K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G)
    (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset))
    (T : Finset K) (g : K →₀ Sym2 V →₀ Nat)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T) :
    kwGraphFormalLogCoeff G phase (g i) =
      MvPowerSeries.coeff (g i)
        (kwWeightedCycleComponentSeries base cycle
          (fun j => cycleCoeff (cycle j).edges.toFinset)) := by
  classical
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  by_cases hexists : exists j : I,
      (g i).support = (cycle j).edges.toFinset
  · obtain ⟨j, hj⟩ := hexists
    have hgi : g i = ons_finsetExponent (cycle j).edges.toFinset := by
      calc
        g i = ons_finsetExponent (g i).support := hcomponent
        _ = ons_finsetExponent (cycle j).edges.toFinset := congrArg _ hj
    rw [hgi, hlog.1 (cycle j) (hcycle j)]
    exact (kwWeightedCycleComponentSeries_coeff_piece
      base cycle (fun j => cycleCoeff (cycle j).edges.toFinset)
        hcycle hdisj j).symm
  · have hleft : kwGraphFormalLogCoeff G phase (g i) = 0 := by
      by_contra hne
      have hcoeffEq : kwGraphFormalLogCoeff G phase
          (ons_finsetExponent (g i).support) ≠ 0 := by
        rw [← hcomponent]
        exact hne
      obtain ⟨root, q, hq, hqedges⟩ := hlog.2 (g i).support hcoeffEq
      have hqsub : q.edges.toFinset ⊆ S := by
        rw [hqedges]
        exact ons_finsuppAntidiag_finsetExponent_support_subset
          T S g hg hi
      obtain ⟨j, hjedges⟩ := ons_cycle_edges_eq_decomposition_piece
        G hdeg S hS base cycle hcycle hcover q hq hqsub
      exact hexists ⟨j, hqedges.symm.trans hjedges⟩
    have hright : MvPowerSeries.coeff (g i)
        (kwWeightedCycleComponentSeries base cycle
          (fun j => cycleCoeff (cycle j).edges.toFinset)) = 0 := by
      rw [kwWeightedCycleComponentSeries_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro heq
      apply hexists
      refine ⟨j, ?_⟩
      apply ons_finsetExponent_injective
      calc
        ons_finsetExponent (g i).support = g i := hcomponent.symm
        _ = ons_finsetExponent (cycle j).edges.toFinset := heq.symm
    rw [hleft, hright]

theorem kwWeightedCycleComponentSeries_pow_coeff
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) (n : Nat) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        ((kwWeightedCycleComponentSeries base cycle coefficient) ^ n) =
      if n = Fintype.card I then
        (n.factorial : Complex) * ∏ i, coefficient i
      else 0 := by
  classical
  let exponent : I -> Sym2 V →₀ Nat :=
    fun i => ons_finsetExponent (cycle i).edges.toFinset
  have hnonempty : forall i, ((cycle i).edges.toFinset).Nonempty :=
    fun i => ons_cycle_edges_toFinset_nonempty (cycle i) (hcycle i)
  have hexponent (f : Fin n -> I) :
      (∑ k, exponent (f k)) = ons_finsetExponent S ↔
        Function.Bijective f := by
    exact ons_sum_finsetExponent_eq_iff_bijective S
      (fun i => (cycle i).edges.toFinset) hcover hdisj hnonempty n f
  have hprod (f : Fin n -> I) :
      (∏ k, MvPowerSeries.monomial
        (exponent (f k)) (coefficient (f k))) =
        MvPowerSeries.monomial (∑ k, exponent (f k))
          (∏ k, coefficient (f k)) := by
    simpa using MvPowerSeries.prod_monomial
      (fun k => exponent (f k)) (fun k => coefficient (f k)) Finset.univ
  have hsumForm :
      MvPowerSeries.coeff (ons_finsetExponent S)
          ((kwWeightedCycleComponentSeries base cycle coefficient) ^ n) =
        ∑ f : Fin n -> I,
          if Function.Bijective f then ∏ k, coefficient (f k) else 0 := by
    unfold kwWeightedCycleComponentSeries
    change MvPowerSeries.coeff (ons_finsetExponent S)
      ((∑ i, MvPowerSeries.monomial (exponent i) (coefficient i)) ^ n) = _
    rw [Fintype.sum_pow, map_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [hprod, MvPowerSeries.coeff_monomial]
    rw [if_congr (by simpa only [eq_comm] using hexponent f) rfl rfl]
  rw [hsumForm]
  by_cases hn : n = Fintype.card I
  · rw [if_pos hn, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hcardEq : Fintype.card (Fin n) = Fintype.card I := by simpa using hn
    let e : Fin n ≃ I := Fintype.equivOfCardEq hcardEq
    have hcardBij :
        Fintype.card {f : Fin n -> I // Function.Bijective f} =
          n.factorial := by
      calc
        Fintype.card {f : Fin n -> I // Function.Bijective f} =
            Fintype.card (Fin n ≃ I) :=
          Fintype.card_congr Equiv.bijectiveEquiv
        _ = (Fintype.card (Fin n)).factorial := Fintype.card_equiv e
        _ = n.factorial := by simp
    have hcardFilter :
        #{f : Fin n -> I | Function.Bijective f} = n.factorial := by
      rw [← Fintype.card_subtype]
      exact hcardBij
    calc
      (∑ f : Fin n -> I with Function.Bijective f,
          ∏ k, coefficient (f k)) =
          ∑ f : Fin n -> I with Function.Bijective f,
            ∏ i, coefficient i := by
        apply Finset.sum_congr rfl
        intro f hf
        exact (Finset.mem_filter.mp hf).2.prod_comp coefficient
      _ = (n.factorial : Complex) * ∏ i, coefficient i := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardFilter]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro f hf
    rw [if_neg]
    intro hbij
    apply hn
    have hcard := Fintype.card_congr (Equiv.ofBijective f hbij)
    simpa using hcard

theorem kwWeightedCycleComponentExp_coeff
    {V I : Type u} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (S : Finset (Sym2 V)) (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex)
    (hcycle : forall i, (cycle i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i => (cycle i).edges.toFinset))
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (cycle i).edges.toFinset)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst
          (kwWeightedCycleComponentSeries base cycle coefficient)
          (PowerSeries.exp Complex)) =
      ∏ i, coefficient i := by
  classical
  rw [PowerSeries.coeff_subst
    (kwWeightedCycleComponentSeries_hasSubst
      base cycle coefficient hcycle)]
  rw [finsum_eq_single _ (Fintype.card I)]
  · rw [kwWeightedCycleComponentSeries_pow_coeff
      S base cycle coefficient hcycle hcover hdisj, if_pos rfl]
    simp only [PowerSeries.coeff_exp, smul_eq_mul]
    rw [one_div, map_inv₀, map_natCast]
    have hfac : ((Fintype.card I).factorial : Complex) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (Fintype.card I)
    field_simp
  · intro n hn
    rw [kwWeightedCycleComponentSeries_pow_coeff
      S base cycle coefficient hcycle hcover hdisj, if_neg hn, smul_zero]


theorem kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex)
    (hlog : KWGraphWeightedCycleLog G phase cycleCoeff)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    exists (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (base : I -> V)
      (cycle : (i : I) -> G.Walk (base i) (base i)),
      (forall i, (cycle i).IsCycle) /\
      S = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset) /\
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => (cycle i).edges.toFinset) /\
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
        (fun i => (cycle i).toSubgraph.verts) /\
      MvPowerSeries.coeff (ons_finsetExponent S)
          (kwGraphFormalRoot G phase) =
        ∏ i, cycleCoeff (cycle i).edges.toFinset := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hweight⟩ :=
    kw_trivalent_even_cycle_weight_decomposition G hdeg S hS
      (fun _ => (1 : Complex))
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  refine ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
    hedgeDisjoint, hvertDisjoint, ?_⟩
  let component := kwWeightedCycleComponentSeries base cycle
    (fun i => cycleCoeff (cycle i).edges.toFinset)
  have heq : MvPowerSeries.coeff (ons_finsetExponent S)
      (kwGraphFormalRoot G phase) =
      MvPowerSeries.coeff (ons_finsetExponent S)
        (PowerSeries.subst component (PowerSeries.exp Complex)) := by
    unfold kwGraphFormalRoot
    rw [PowerSeries.coeff_subst (kwGraphFormalLog_hasSubst G phase),
      PowerSeries.coeff_subst
        (kwWeightedCycleComponentSeries_hasSubst base cycle _ hcycle)]
    apply finsum_congr
    intro n
    congr 1
    apply kwMvPowerSeries_coeff_pow_eq_of_antidiag
    intro g hg i hi
    change kwGraphFormalLogCoeff G phase (g i) = _
    exact kwGraphFormalLog_coeff_eq_weightedCycleComponent_of_antidiag
      (G := G) (phase := phase) (cycleCoeff := cycleCoeff)
      (hlog := hlog) (hdeg := hdeg) (S := S) (hS := hS)
      (base := base) (cycle := cycle) (hcycle := hcycle)
      (hcover := hcover) (hdisj := hedgeDisjoint)
      (T := Finset.range n) (g := g) hg hi
  rw [heq]
  exact kwWeightedCycleComponentExp_coeff
    S base cycle _ hcycle hcover hedgeDisjoint

theorem surfaceIntersection_add_right {g : Nat}
    (h k l : SurfaceHomology g) :
    surfaceIntersection h (k + l) =
      surfaceIntersection h k + surfaceIntersection h l := by
  unfold surfaceIntersection
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_add]
  abel

theorem surfaceIntersection_finset_sum_right {g : Nat}
    {I : Type*} [DecidableEq I] (h : SurfaceHomology g)
    (S : Finset I) (f : I -> SurfaceHomology g) :
    surfaceIntersection h (∑ i ∈ S, f i) =
      ∑ i ∈ S, surfaceIntersection h (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [surfaceIntersection]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceIntersection_add_right, ih]

theorem surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero
    {g : Nat} {I : Type*} [DecidableEq I]
    (lambda : SurfaceSpinStructure g) (S : Finset I)
    (f : I -> SurfaceHomology g)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
      surfaceIntersection (f i) (f j) = 0) :
    surfaceQuadraticParity lambda (∑ i ∈ S, f i) =
      ∑ i ∈ S, surfaceQuadraticParity lambda (f i) := by
  induction S using Finset.induction_on with
  | empty => simp [surfaceQuadraticParity]
  | @insert i S hi ih =>
      have hpairS : ∀ j ∈ S, ∀ k ∈ S, j ≠ k ->
          surfaceIntersection (f j) (f k) = 0 := by
        intro j hj k hk hjk
        exact hpair j (by simp [hj]) k (by simp [hk]) hjk
      have hinter : surfaceIntersection (f i) (∑ j ∈ S, f j) = 0 := by
        rw [surfaceIntersection_finset_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact hpair i (by simp) j (by simp [hj]) (by
          intro hij
          subst j
          exact hi hj)
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceQuadraticParity_add, hinter, add_zero, ih hpairS]

theorem surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero
    {g : Nat} {I : Type*} [DecidableEq I]
    (lambda : SurfaceSpinStructure g) (S : Finset I)
    (f : I -> SurfaceHomology g)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
      surfaceIntersection (f i) (f j) = 0) :
    (surfaceParitySign
      (surfaceQuadraticParity lambda (∑ i ∈ S, f i)) : Complex) =
      ∏ i ∈ S,
        (surfaceParitySign (surfaceQuadraticParity lambda (f i)) : Complex) := by
  rw [surfaceQuadraticParity_finset_sum_of_pairwise_intersection_zero
    lambda S f hpair, surfaceParitySign_finset_sum]
  push_cast
  rfl

theorem surfaceSubgraphHomology_biUnion
    {g : Nat} {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) (piece : I -> Finset (Sym2 V))
    (hcover : S = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint piece) :
    surfaceSubgraphHomology edgeClass S =
      ∑ i, surfaceSubgraphHomology edgeClass (piece i) := by
  classical
  unfold surfaceSubgraphHomology
  rw [hcover, Finset.sum_biUnion hdisj]


end StatMech.FrontierA
