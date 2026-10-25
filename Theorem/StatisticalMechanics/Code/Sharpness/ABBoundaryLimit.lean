/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

@[simp] theorem abbl_abbEdgeEquiv_symm_mk {U W : Type*}
    (sigma : U ≃ W) (a b : W) :
    (abbEdgeEquiv sigma).symm s(a, b) = s(sigma.symm a, sigma.symm b) := by
  apply (abbEdgeEquiv sigma).injective
  simp [abbEdgeEquiv_mk]

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 800000 in


theorem abbl_residual_le_exp (J : Sym2 V → Real) (o : V)
    (beta h : Real) (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (k : Nat)
    (R : Set (ConfigSpace (Sym2 (Option V))))
    (hRghost : R ⊆
      (connEvent (withGhost G) Set.univ (some o) {none})ᶜ)
    (hcard : ∀ eta : {e // e ∉ FieldGhostDict.ghostEdges V} → Bool,
      ∀ gamma : {e // e ∈ FieldGhostDict.ghostEdges V} → Bool,
        abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈ R →
          k ≤ (abgrActiveGhost G o eta).card) :
    probV (abfaParams G J beta h) R ≤
      Real.exp (-(h * (k : Real))) := by
  let D := FieldGhostDict.ghostEdges V
  let q := qField h
  let p : Sym2 (Option V) → Real := fun e ↦
    pBeta (abfaLiftCoupling G J e) beta
  have hq0 : 0 ≤ q := (qField_mem h hh).1
  have hq1 : q ≤ 1 := (qField_mem h hh).2
  have hsplit :
      probV (abfaParams G J beta h) R =
        ∑ eta : {e // e ∉ D} → Bool,
          abgrOffWeight G J beta eta *
            probV (fun _ : {e // e ∈ D} ↦ q)
              {gamma | abgrMerge D gamma eta ∈ R} := by
    unfold abfaParams abpdBetaFieldParams
    simpa only [D, q, p, abgrOffWeight] using
      (abgr_probV_split D q p R)
  rw [hsplit]
  have hsection : ∀ eta : {e // e ∉ D} → Bool,
      probV (fun _ : {e // e ∈ D} ↦ q)
          {gamma | abgrMerge D gamma eta ∈ R} ≤
        Real.exp (-(h * (k : Real))) := by
    intro eta
    by_cases hne : ({gamma | abgrMerge D gamma eta ∈ R} :
        Set ({e // e ∈ D} → Bool)).Nonempty
    · obtain ⟨gamma0, hgamma0⟩ := hne
      have hk : k ≤ (abgrActiveGhost G o eta).card :=
        hcard eta gamma0 hgamma0
      let C : Set ({e // e ∈ D} → Bool) :=
        {gamma | ∀ e ∈ abgrActiveGhost G o eta, gamma e = false}
      have hsub : {gamma | abgrMerge D gamma eta ∈ R} ⊆ C := by
        intro gamma hgamma e he
        by_contra hopen
        have hopen' : gamma e = true := by
          cases hge : gamma e <;> simp_all
        have hconn : abgrMerge D gamma eta ∈
            connEvent (withGhost G) Set.univ (some o) {none} :=
          (abgr_section_iff_anyOpen G o gamma eta).mpr ⟨e, he, hopen'⟩
        exact (hRghost hgamma) hconn
      have hmono := abgi_probV_mono (fun _ : {e // e ∈ D} ↦ q)
        (fun _ ↦ ⟨hq0, hq1⟩) hsub
      have hclosed :
          probV (fun _ : {e // e ∈ D} ↦ q) C =
            Real.exp (-(h * ((abgrActiveGhost G o eta).card : Real))) := by
        rw [show C = {gamma | ∀ e ∈ abgrActiveGhost G o eta,
            gamma e = false} by rfl,
          abgr_probV_allClosed]
        have hprofile := abgr_cluster_profile_eq_exp h
          (abgrActiveGhost G o eta).card
        simp only [q, qField, sub_sub_cancel, Finset.prod_const,
          Finset.card_attach] at hprofile ⊢
        linarith
      rw [hclosed] at hmono
      exact hmono.trans (Real.exp_le_exp.mpr (by
        have hcast : (k : Real) ≤ (abgrActiveGhost G o eta).card := by
          exact_mod_cast hk
        nlinarith))
    · have hempty : {gamma | abgrMerge D gamma eta ∈ R} =
          (∅ : Set ({e // e ∈ D} → Bool)) := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp only [probV, Set.indicator_empty, zero_mul, Finset.sum_const_zero]
      exact (Real.exp_pos _).le
  calc
    (∑ eta : {e // e ∉ D} → Bool,
        abgrOffWeight G J beta eta *
          probV (fun _ : {e // e ∈ D} ↦ q)
            {gamma | abgrMerge D gamma eta ∈ R}) ≤
      ∑ eta : {e // e ∉ D} → Bool,
        abgrOffWeight G J beta eta *
          Real.exp (-(h * (k : Real))) := by
      apply Finset.sum_le_sum
      intro eta heta
      exact mul_le_mul_of_nonneg_left (hsection eta)
        (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = Real.exp (-(h * (k : Real))) := by
      rw [← Finset.sum_mul, abgr_sum_offWeight G J beta, one_mul]


theorem abbl_closeGhost_conn_of_not_ghost (o y : V)
    (omega : ConfigSpace (Sym2 (Option V)))
    (hconn : omega ∈
      connEvent (withGhost G) Set.univ (some o) {some y})
    (hnot : omega ∉
      connEvent (withGhost G) Set.univ (some o) {none}) :
    abgrCloseGhost omega ∈
      connEvent (withGhost G) Set.univ (some o) {some y} := by
  obtain ⟨_, z, _, hz, ⟨p⟩⟩ := hconn
  have hzy : z = some y := Set.mem_singleton_iff.mp hz
  subst z
  let q : (openSub (withGhost G) omega).Walk (some o) (some y) :=
    p.map (SimpleGraph.Embedding.induce Set.univ).toHom
  have hnone : none ∉ q.support := by
    intro hn
    apply hnot
    refine ⟨Set.mem_univ _, none, Set.mem_univ _, rfl, ?_⟩
    exact (q.takeUntil none hn).reachable.elim fun w ↦
      ⟨w.induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩
  have htransfer : ∀ {a b : Option V}
      (w : (openSub (withGhost G) omega).Walk a b),
      none ∉ w.support →
        (openSub (withGhost G) (abgrCloseGhost omega)).Walk a b := by
    intro a b w
    induction w with
    | nil =>
        intro h
        exact .nil
    | @cons a b c hab w ih =>
        intro hnone'
        have hnonea : a ≠ none := by
          intro ha
          apply hnone'
          exact ha ▸ (SimpleGraph.Walk.cons hab w).start_mem_support
        have hnoneb : b ≠ none := by
          intro hb
          apply hnone'
          have hbmem : b ∈ (SimpleGraph.Walk.cons hab w).support := by
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ w.start_mem_support
          exact hb ▸ hbmem
        rcases a with _ | a
        · exact False.elim (hnonea rfl)
        · rcases b with _ | b
          · exact False.elim (hnoneb rfl)
          · apply SimpleGraph.Walk.cons
            · refine ⟨hab.1, ?_⟩
              simpa using hab.2
            · apply ih
              intro hn
              apply hnone'
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ hn
  refine ⟨Set.mem_univ _, some y, Set.mem_univ _, rfl, ?_⟩
  exact ⟨(htransfer q hnone).induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩


theorem abbl_le_l1dist_origin_of_boundary {d n : Nat} (hn : 0 < n)
    {y : Site d} (hy : y ∈ vertexBoundary d n) :
    n ≤ l1dist d (origin d) y := by
  obtain ⟨hybox, hyinner⟩ := hy
  rw [mem_box] at hybox
  rw [mem_box] at hyinner
  push_neg at hyinner
  obtain ⟨i, hi⟩ := hyinner
  have hni : n ≤ (y i).natAbs := by omega
  have hterm : (y i).natAbs = ((origin d) i - y i).natAbs := by
    simp [origin, Int.natAbs_neg]
  rw [hterm] at hni
  exact hni.trans (Finset.single_le_sum
    (fun j hj ↦ Nat.zero_le (((origin d) j - y j).natAbs))
    (Finset.mem_univ i))


theorem abbl_activeGhost_card_ge_of_boundary {d n : Nat} (hn : 0 < n)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (y : sctBox d n) (hy : (y : Site d) ∈ vertexBoundary d n)
    (hconn : abgrCloseGhost
      (abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta) ∈
        connEvent (withGhost (sctBoxGraph d n)) Set.univ
          (some (sctBoxOrigin d n)) {some y}) :
    n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n)
      (sctBoxOrigin d n) eta).card := by
  let omega := abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta
  let omega0 := abgrCloseGhost omega
  let phys : ConfigSpace (Sym2 (sctBox d n)) := fun e ↦
    omega0 (Sym2.map some e)
  obtain ⟨_, z, _, hz, ⟨p⟩⟩ := hconn
  have hzy : z = some y := Set.mem_singleton_iff.mp hz
  subst z
  let q : (openSub (withGhost (sctBoxGraph d n)) omega0).Walk
      (some (sctBoxOrigin d n)) (some y) :=
    p.map (SimpleGraph.Embedding.induce Set.univ).toHom
  have hphysical : ∀ {u v : Option (sctBox d n)}
      (w : (openSub (withGhost (sctBoxGraph d n)) omega0).Walk u v)
      (a b : sctBox d n), u = some a → v = some b →
        (openSub (sctBoxGraph d n) phys).Walk a b := by
    intro u v w
    induction w with
    | @nil u =>
        intro a b hua hub
        have hab : a = b := Option.some.inj (hua.symm.trans hub)
        subst b
        exact .nil
    | @cons u v z huv tail ih =>
        intro a b hua hzb
        subst u
        rcases v with _ | v
        · have : omega0 s(some a, none) = false := by
            simp [omega0, omega]
          have htf : true = false := huv.2.symm.trans this
          exact False.elim (by simp at htf)
        · apply SimpleGraph.Walk.cons
          · refine ⟨?_, ?_⟩
            · simpa [withGhost] using huv.1
            · simpa [phys, Sym2.map_mk] using huv.2
          · exact ih v b rfl hzb
  let w := hphysical q (sctBoxOrigin d n) y rfl rfl
  let path : (openSub (sctBoxGraph d n) phys).Walk
      (sctBoxOrigin d n) y := w.toPath
  have hpath : path.IsPath := w.toPath.2
  let lift : openSub (sctBoxGraph d n) phys →g
      openSub (withGhost (sctBoxGraph d n)) omega0 :=
    { toFun := some
      map_rel' := fun {a b} hab ↦ by
        refine ⟨?_, ?_⟩
        · simpa [withGhost] using hab.1
        · simpa [phys, Sym2.map_mk] using hab.2 }
  have hsupp : path.support.toFinset ⊆
      abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega := by
    intro x hx
    rw [List.mem_toFinset] at hx
    simp only [abgrActive, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Set.mem_univ _, some x, Set.mem_univ _, rfl, ?_⟩
    let px := path.takeUntil x hx
    exact ⟨(px.map lift).induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩
  have hcardPath : path.support.toFinset.card = path.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup,
      SimpleGraph.Walk.length_support]
  let forget : openSub (sctBoxGraph d n) phys →g hypercubicLattice d :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab ↦ by
        simpa [sctBoxGraph] using hab.1 }
  have hlen : n ≤ path.length := by
    have hdist := abbl_le_l1dist_origin_of_boundary hn hy
    have hwalk := l1dist_le_walk_length d (path.map forget)
    simpa [path, forget, sctBoxOrigin] using hdist.trans hwalk
  have hactiveCard : path.support.toFinset.card ≤
      (abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega).card :=
    Finset.card_le_card hsupp
  have hghostCard :
      (abgrActiveGhost (sctBoxGraph d n) (sctBoxOrigin d n) eta).card =
        (abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega).card := by
    simp only [abgrActiveGhost, Finset.card_map]
    rw [abgrActive_merge_eq (sctBoxGraph d n) (sctBoxOrigin d n) gamma eta]
  rw [hghostCard]
  omega


end Sharpness
end StatMech
