/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound.Part2
open scoped BigOperators
open Finset Filter Topology Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bond_abs_le_one_general (s : ConfigSpace V) (e : Sym2 V) : |bond s e| ≤ 1 := by
  induction e using Sym2.ind with
  | _ x y =>
      rw [bond_mk, abs_mul]
      nlinarith [abs_spin_le_one s x, abs_spin_le_one s y,
        abs_nonneg (spin s x), abs_nonneg (spin s y)]


theorem isingHamiltonian_sub_abs_le_edgeDiff
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (h : ℝ) (s : ConfigSpace V) :
    |hamiltonian G h s - hamiltonian H h s| ≤ (G.edgeFinset \ H.edgeFinset).card := by
  have hsub : H.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hHG
  have hsplit :
      (∑ e ∈ G.edgeFinset, bond s e) - ∑ e ∈ H.edgeFinset, bond s e =
        ∑ e ∈ G.edgeFinset \ H.edgeFinset, bond s e := by
    rw [← Finset.sum_sdiff hsub]
    ring
  have heq : hamiltonian G h s - hamiltonian H h s =
      -((∑ e ∈ G.edgeFinset, bond s e) - ∑ e ∈ H.edgeFinset, bond s e) := by
    unfold hamiltonian
    ring
  rw [heq, abs_neg, hsplit]
  calc
    |∑ e ∈ G.edgeFinset \ H.edgeFinset, bond s e| ≤
        ∑ e ∈ G.edgeFinset \ H.edgeFinset, |bond s e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G.edgeFinset \ H.edgeFinset, (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ => bond_abs_le_one_general s e)
    _ = (G.edgeFinset \ H.edgeFinset).card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem isingLogZ_sub_abs_le_edgeDiff
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (beta h : ℝ) :
    |Real.log (isingZ G beta h) - Real.log (isingZ H beta h)| ≤
      |beta| * (G.edgeFinset \ H.edgeFinset).card := by
  exact logZ_dist_le beta (hamiltonian G h) (hamiltonian H h)
    ((G.edgeFinset \ H.edgeFinset).card)
    (isingHamiltonian_sub_abs_le_edgeDiff G H hHG h)

theorem isingSum_edgeCard
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  rw [fsm_edgeFinset_sum, Finset.card_union_of_disjoint (fsm_images_disjoint G H),
    Finset.card_image_of_injective _ fsm_map_inl_injective,
    Finset.card_image_of_injective _ fsm_map_inr_injective]


theorem agl_interfaceCard_add_edgeCards
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P] :
    agl_interfaceCard G P + (agl_left G P).edgeFinset.card +
        (agl_right G P).edgeFinset.card = G.edgeFinset.card := by
  let L := agl_left G P
  let R := agl_right G P
  let K := agl_glueGraph G P
  have hsub : (L ⊕g R).edgeFinset ⊆ K.edgeFinset :=
    SimpleGraph.edgeFinset_mono (agl_partitionCrossInterface G P).le
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hiso := (agl_iso G P).card_edgeFinset_eq
  have hsum := isingSum_edgeCard L R
  change G.edgeFinset.card = K.edgeFinset.card at hiso
  change (K.edgeFinset \ (L ⊕g R).edgeFinset).card +
      L.edgeFinset.card + R.edgeFinset.card = G.edgeFinset.card
  omega


theorem isingLogZ_partition_sub_abs_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P] (beta h : ℝ) :
    |Real.log (isingZ G beta h) -
        (Real.log (isingZ (agl_left G P) beta h) +
          Real.log (isingZ (agl_right G P) beta h))| ≤
      |beta| * agl_interfaceCard G P := by
  let L := agl_left G P
  let R := agl_right G P
  let K := agl_glueGraph G P
  have hcomp := isingLogZ_sub_abs_le_edgeDiff K (L ⊕g R)
    (agl_partitionCrossInterface G P).le beta h
  have hG : isingZ G beta h = isingZ K beta h := by
    exact isingZ_relabel G K (agl_iso G P).toEquiv
      (fun x y => (agl_iso G P).map_rel_iff.symm) beta h
  have hsum : Real.log (isingZ (L ⊕g R) beta h) =
      Real.log (isingZ L beta h) + Real.log (isingZ R beta h) := by
    rw [isingZ_sum, Real.log_mul (isingZ_ne_zero L beta h) (isingZ_ne_zero R beta h)]
  simpa only [hG, hsum, agl_interfaceCard, L, R, K] using hcomp


theorem isingZ_empty {W : Type*} [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (beta h : ℝ) :
    isingZ G beta h = 1 := by
  unfold isingZ
  have hs : Subsingleton (ConfigSpace W) :=
    ⟨fun a b => funext (fun x => isEmptyElim x)⟩
  have hedge : G.edgeFinset = ∅ := by
    rw [SimpleGraph.edgeFinset_eq_empty]
    ext x y
    exact ⟨fun _ => isEmptyElim x, fun hx => hx.elim⟩
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [isingWeight, hamiltonian, hedge]
  · intro b _ hb
    exact absurd (Subsingleton.elim b (fun _ => false)) hb
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

section TagPeel

variable {T : Type*} [DecidableEq T]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (tag : V → T)

theorem isingZ_left_tag (tau : T) (S : Finset T) (htau : tau ∉ S) (beta h : ℝ) :
    isingZ (agl_left (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h =
      isingZ (qp_blkG G tag tau) beta h := by
  let phi := qp_comapComapIso G
    (Subtype.val : {x : V // tag x ∈ insert tau S} → V)
    (Subtype.val : {x : {x : V // tag x ∈ insert tau S} // tag x.1 = tau} → _)
    (Subtype.val : {x : V // tag x = tau} → V)
    (by intro a b hab; apply Subtype.ext; apply Subtype.ext; exact hab)
    Subtype.val_injective
    (by
      ext u
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨⟨v.1, v.2⟩, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self tau S⟩, v.2⟩, rfl⟩)
  exact isingZ_relabel _ _ phi.toEquiv
    (fun x y => phi.map_rel_iff.symm) beta h

theorem isingZ_right_tag (tau : T) (S : Finset T) (htau : tau ∉ S) (beta h : ℝ) :
    isingZ (agl_right (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h =
      isingZ (qp_restG G tag S) beta h := by
  let phi := qp_comapComapIso G
    (Subtype.val : {x : V // tag x ∈ insert tau S} → V)
    (Subtype.val : {x : {x : V // tag x ∈ insert tau S} // ¬ tag x.1 = tau} → _)
    (Subtype.val : {x : V // tag x ∈ S} → V)
    (by intro a b hab; apply Subtype.ext; apply Subtype.ext; exact hab)
    Subtype.val_injective
    (by
      ext u
      constructor
      · rintro ⟨v, rfl⟩
        have hv := v.1.2
        rw [Finset.mem_insert] at hv
        rcases hv with hv | hv
        · exact absurd hv v.2
        · exact ⟨⟨v.1.1, hv⟩, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩,
          fun hc => htau (hc ▸ v.2)⟩, rfl⟩)
  exact isingZ_relabel _ _ phi.toEquiv
    (fun x y => phi.map_rel_iff.symm) beta h


theorem isingLogZ_tagPeel (beta h : ℝ) : ∀ S : Finset T, ∃ I : ℕ,
    |Real.log (isingZ (qp_restG G tag S) beta h) -
      ∑ tau ∈ S, Real.log (isingZ (qp_blkG G tag tau) beta h)| ≤ |beta| * I ∧
    I + ∑ tau ∈ S, (qp_blkG G tag tau).edgeFinset.card =
      (qp_restG G tag S).edgeFinset.card := by
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · haveI : IsEmpty {x : V // tag x ∈ (∅ : Finset T)} :=
          ⟨fun x => by simpa using x.2⟩
        rw [Finset.sum_empty, isingZ_empty, Real.log_one]
        simp
      · haveI : IsEmpty {x : V // tag x ∈ (∅ : Finset T)} :=
          ⟨fun x => by simpa using x.2⟩
        simp only [Finset.sum_empty, add_zero]
        have hedge : (qp_restG G tag (∅ : Finset T)).edgeFinset = ∅ := by
          rw [SimpleGraph.edgeFinset_eq_empty]
          ext x y
          exact ⟨fun _ => isEmptyElim x, fun hx => hx.elim⟩
        rw [hedge, Finset.card_empty]
  | @insert tau S htau ih =>
      obtain ⟨I0, hI0, hcard0⟩ := ih
      let R := qp_restG G tag (insert tau S)
      let P : {x : V // tag x ∈ insert tau S} → Prop := fun x => tag x.1 = tau
      let Is := agl_interfaceCard R P
      refine ⟨Is + I0, ?_, ?_⟩
      · rw [Finset.sum_insert htau]
        have hpart := isingLogZ_partition_sub_abs_le R P beta h
        rw [isingZ_left_tag G tag tau S htau,
          isingZ_right_tag G tag tau S htau] at hpart
        calc
          |Real.log (isingZ R beta h) -
              (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h))| =
              |(Real.log (isingZ R beta h) -
                  (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                    Real.log (isingZ (qp_restG G tag S) beta h))) +
                (Real.log (isingZ (qp_restG G tag S) beta h) -
                  ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h))| := by
                congr 1 <;> ring
          _ ≤ |Real.log (isingZ R beta h) -
                  (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                    Real.log (isingZ (qp_restG G tag S) beta h))| +
                |Real.log (isingZ (qp_restG G tag S) beta h) -
                  ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h)| :=
              abs_add_le _ _
          _ ≤ |beta| * Is + |beta| * I0 := add_le_add hpart hI0
          _ = |beta| * ((Is : ℝ) + (I0 : ℝ)) := by ring
          _ = |beta| * ((Is + I0 : ℕ) : ℝ) := by norm_num
      · rw [Finset.sum_insert htau]
        have hpart := agl_interfaceCard_add_edgeCards R P
        rw [ecz_left_edge_card G tag tau S htau,
          ecz_right_edge_card G tag tau S htau] at hpart
        change Is + I0 +
            ((qp_blkG G tag tau).edgeFinset.card +
              ∑ sigma ∈ S, (qp_blkG G tag sigma).edgeFinset.card) = R.edgeFinset.card
        omega

end TagPeel


theorem isingLogZ_abs_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : ℝ) :
    |Real.log (isingZ G beta h)| ≤
      (Fintype.card V : ℝ) * Real.log 2 +
        |beta| * ((G.edgeFinset.card : ℝ) + |h| * Fintype.card V) := by
  let E : ConfigSpace V → ℝ := fun s => -beta * hamiltonian G h s
  let M : ℝ := |beta| * ((G.edgeFinset.card : ℝ) + |h| * Fintype.card V)
  have hE : ∀ s, |E s| ≤ M := by
    intro s
    have hb : |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| ≤ G.edgeFinset.card := by
      calc
        |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| ≤
            ∑ e ∈ G.edgeFinset, |bond s e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _e ∈ G.edgeFinset, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => bond_abs_le_one_general s e)
        _ = G.edgeFinset.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs : |(∑ v : V, spin s v : ℝ)| ≤ Fintype.card V := by
      calc
        |(∑ v : V, spin s v : ℝ)| ≤ ∑ v : V, |spin s v| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : V, (1 : ℝ) :=
          Finset.sum_le_sum (fun v _ => abs_spin_le_one s v)
        _ = Fintype.card V := by simp
    unfold E M hamiltonian
    rw [abs_mul]
    have hhamm : |-((∑ e ∈ G.edgeFinset, bond s e : ℝ)) -
        h * ∑ v : V, spin s v| ≤
        (G.edgeFinset.card : ℝ) + |h| * Fintype.card V := by
      calc
        |-((∑ e ∈ G.edgeFinset, bond s e : ℝ)) - h * ∑ v : V, spin s v| ≤
            |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| +
              |h| * |(∑ v : V, spin s v : ℝ)| := by
                simpa [abs_mul] using abs_add_le
                  (-(∑ e ∈ G.edgeFinset, bond s e : ℝ))
                  (-h * ∑ v : V, spin s v)
        _ ≤ (G.edgeFinset.card : ℝ) + |h| * Fintype.card V := by
          gcongr
    rw [abs_neg]
    exact mul_le_mul_of_nonneg_left hhamm (abs_nonneg beta)
  have hlow : Real.exp (-M) * Fintype.card (ConfigSpace V) ≤ isingZ G beta h := by
    change Real.exp (-M) * Fintype.card (ConfigSpace V) ≤ ∑ s, Real.exp (E s)
    calc
      Real.exp (-M) * Fintype.card (ConfigSpace V) =
          ∑ _s : ConfigSpace V, Real.exp (-M) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ ≤ ∑ s, Real.exp (E s) := Finset.sum_le_sum (fun s _ =>
        Real.exp_le_exp.mpr (neg_le_of_abs_le (hE s)))
  have hupp : isingZ G beta h ≤ Real.exp M * Fintype.card (ConfigSpace V) := by
    change (∑ s, Real.exp (E s)) ≤ Real.exp M * Fintype.card (ConfigSpace V)
    calc
      (∑ s, Real.exp (E s)) ≤ ∑ _s : ConfigSpace V, Real.exp M :=
        Finset.sum_le_sum (fun s _ => Real.exp_le_exp.mpr (le_of_abs_le (hE s)))
      _ = Real.exp M * Fintype.card (ConfigSpace V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hcard : (Fintype.card (ConfigSpace V) : ℝ) = 2 ^ Fintype.card V := by
    simp [ConfigSpace, Fintype.card_bool]
  have hloglow := Real.log_le_log (mul_pos (Real.exp_pos _) (by positivity)) hlow
  have hlogupp := Real.log_le_log (isingZ_pos G beta h) hupp
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    hcard, Real.log_pow] at hloglow hlogupp
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hVlog : 0 ≤ (Fintype.card V : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) hlog2
  change |Real.log (isingZ G beta h)| ≤
    (Fintype.card V : ℝ) * Real.log 2 + M
  rw [abs_le]
  constructor <;> linarith


end StatMech.FrontierA
