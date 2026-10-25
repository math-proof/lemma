/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


theorem kwGraphLoopOrientation_mem_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (orientation : Fin n ⊕ Fin n) :
    kwGraphLoopOrientation loop orientation ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop ⊢
  cases orientation with
  | inl k =>
      exact ⟨(kwGraphLoopExponent_rotate G loop k).trans hloop.1,
        by simpa [kwGraphLoopOrientation, kwGraphLoopScalar_rotate]
          using hloop.2⟩
  | inr k =>
      refine ⟨?_, ?_⟩
      · rw [kwGraphLoopOrientation, kwGraphLoopExponent_rotate,
          kwGraphLoopExponent_loopRev, hloop.1]
      · rw [kwGraphLoopOrientation, kwGraphLoopScalar_rotate,
          kwGraphLoopScalar_loopRev_straightLine]
        exact hloop.2

theorem kwGraphLoopOrientation_injective_of_squarefree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    Function.Injective (kwGraphLoopOrientation loop) := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have htrail := kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1
  have hedgeNodup :
      ((List.ofFn loop).map SimpleGraph.Dart.edge).Nodup := by
    rw [← kwGraphLoopWalk_edges G loop hvalid]
    exact htrail.1.edges_nodup
  rw [← List.ofFn_comp'] at hedgeNodup
  have hedgeInj : Function.Injective
      (fun k : Fin n ↦ (loop k).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  intro x y hxy
  have hzero := congrFun hxy 0
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          exact congrArg Sum.inl (hedgeInj
            (congrArg (fun dart : G.Dart ↦ dart.edge)
              (by simpa [kwGraphLoopOrientation, ons_rotate] using hzero)))
      | inr j =>
          exfalso
          have hbad : loop i = (loop (-j)).symm := by
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using hzero
          have hij : i = -j := by
            apply hedgeInj
            calc
              (loop i).edge = ((loop (-j)).symm).edge :=
                congrArg (fun dart : G.Dart ↦ dart.edge) hbad
              _ = (loop (-j)).edge := SimpleGraph.Dart.edge_symm _
          have hself : loop i = (loop i).symm :=
            hbad.trans (congrArg SimpleGraph.Dart.symm
              (congrArg loop hij.symm))
          exact (loop i).symm_ne hself.symm
  | inr i =>
      cases y with
      | inl j =>
          exfalso
          have hbad : loop j = (loop (-i)).symm := by
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using hzero.symm
          have hji : j = -i := by
            apply hedgeInj
            calc
              (loop j).edge = ((loop (-i)).symm).edge :=
                congrArg (fun dart : G.Dart ↦ dart.edge) hbad
              _ = (loop (-i)).edge := SimpleGraph.Dart.edge_symm _
          have hself : loop j = (loop j).symm :=
            hbad.trans (congrArg SimpleGraph.Dart.symm
              (congrArg loop hji.symm))
          exact (loop j).symm_ne hself.symm
      | inr j =>
          have hrev : loop (-i) = loop (-j) := by
            have := congrArg SimpleGraph.Dart.symm hzero
            simpa [kwGraphLoopOrientation, ons_rotate,
              kwGraphLoopRev, ons_involutiveLoopRev] using this
          have hneg : -i = -j :=
            hedgeInj (congrArg (fun dart : G.Dart ↦ dart.edge) hrev)
          exact congrArg Sum.inr (by
            simpa using congrArg Neg.neg hneg)

theorem kwGraphSquarefreeLoopFinset_card_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    (kwGraphSquarefreeLoopFinset (n := n)
      G embedding.turnPhase S).card = 2 * n := by
  let loops := kwGraphSquarefreeLoopFinset (n := n)
    G embedding.turnPhase S
  let roots := loops.image (fun e ↦ e 0)
  have hcardRoots : roots.card = loops.card := by
    apply Finset.card_image_of_injOn
    exact kwGraph_squarefreeLoop_eval_zero_injective
      G embedding.turnPhase hdeg S
  have hsubset : roots ⊆ kwGraphLoopRootFinset loop := by
    intro root hroot
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hroot
    apply kwGraph_root_mem_loopRootFinset
      G embedding.turnPhase S hloop (e 0)
    exact kwGraph_squarefreeLoop_root_edge_mem
      G embedding.turnPhase S he
  have hle : loops.card ≤ 2 * n := by
    calc
      loops.card = roots.card := hcardRoots.symm
      _ ≤ (kwGraphLoopRootFinset loop).card := Finset.card_le_card hsubset
      _ = 2 * n := kwGraphLoopRootFinset_card_of_squarefree
        G embedding.turnPhase S hloop
  have hge : 2 * n ≤ loops.card := by
    let orient : Fin n ⊕ Fin n → {e // e ∈ loops} := fun k ↦
      ⟨kwGraphLoopOrientation loop k,
        kwGraphLoopOrientation_mem_straightLine
          G embedding S hloop k⟩
    have horient : Function.Injective orient := by
      intro i j hij
      apply kwGraphLoopOrientation_injective_of_squarefree
        G embedding.turnPhase S hloop
      exact congrArg Subtype.val hij
    have hcard := Fintype.card_le_of_injective orient horient
    simpa [loops, Fintype.card_sum, two_mul] using hcard
  exact Nat.le_antisymm hle hge

theorem kwGraphSquarefreeLoop_scalar_eq_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d e : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (he : e ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    kwGraphLoopScalar G embedding.turnPhase e =
      kwGraphLoopScalar G embedding.turnPhase d := by
  have hrootEdge := kwGraph_squarefreeLoop_root_edge_mem
    G embedding.turnPhase S he
  have hroot := kwGraph_root_mem_loopRootFinset
    G embedding.turnPhase S hd (e 0) hrootEdge
  unfold kwGraphLoopRootFinset at hroot
  rw [Finset.mem_union] at hroot
  have hinj := kwGraph_squarefreeLoop_eval_zero_injective (n := n)
    G embedding.turnPhase hdeg S
  rcases hroot with hroot | hroot
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_straightLine
      G embedding S hd (Sum.inl k)
    have heq : e = ons_rotate k d := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate]
  · obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hroot
    have hrot := kwGraphLoopOrientation_mem_straightLine
      G embedding S hd (Sum.inr (-k))
    have heq : e = ons_rotate (-k) (kwGraphLoopRev d) := by
      apply hinj he hrot
      simpa [kwGraphLoopOrientation, ons_rotate,
        kwGraphLoopRev, ons_involutiveLoopRev] using hk.symm
    rw [heq, kwGraphLoopScalar_rotate,
      kwGraphLoopScalar_loopRev_straightLine]

theorem kwGraphSquarefreeLoop_bucket_sum_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {d : Fin n → G.Dart}
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G embedding.turnPhase e else 0) =
      (2 * n : ℂ) * kwGraphLoopScalar G embedding.turnPhase d := by
  classical
  let loops := kwGraphSquarefreeLoopFinset (n := n)
    G embedding.turnPhase S
  calc
    (∑ e : Fin n → G.Dart,
      if kwGraphLoopExponent G e = ons_finsetExponent S then
        kwGraphLoopScalar G embedding.turnPhase e else 0) =
        ∑ e ∈ loops, kwGraphLoopScalar G embedding.turnPhase e := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subset
      · intro e he
        simp only [loops, kwGraphSquarefreeLoopFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e heExp heNot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heExp
        by_contra hscalar
        apply heNot
        simp [loops, kwGraphSquarefreeLoopFinset, heExp, hscalar]
    _ = ∑ _e ∈ loops, kwGraphLoopScalar G embedding.turnPhase d := by
      apply Finset.sum_congr rfl
      intro e he
      exact kwGraphSquarefreeLoop_scalar_eq_straightLine
        G embedding hdeg S hd he
    _ = (2 * n : ℂ) * kwGraphLoopScalar G embedding.turnPhase d := by
      rw [Finset.sum_const, nsmul_eq_mul,
        kwGraphSquarefreeLoopFinset_card_straightLine
          G embedding hdeg S hd]
      norm_cast


theorem kwGraphFormalLogCoeff_squarefree_of_mem_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (r : ℕ)
    (d : Fin (r + 1) → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) =
      -kwGraphLoopScalar G embedding.turnPhase d := by
  have hddata := (kwGraph_mem_squarefreeLoopFinset
    G embedding.turnPhase S d).mp hd
  have hdegree : ons_finsuppTotalDegree (ons_finsetExponent S) = r + 1 := by
    rw [← hddata.1]
    exact kwGraphLoopExponent_totalDegree G d
  have hrange : r ∈ Finset.range
      (ons_finsuppTotalDegree (ons_finsetExponent S)) := by
    rw [Finset.mem_range, hdegree]
    omega
  unfold kwGraphFormalLogCoeff
  rw [Finset.sum_eq_single r]
  · rw [kwGraphSquarefreeLoop_bucket_sum_straightLine
      G embedding hdeg S hd]
    push_cast
    field_simp
  · intro r' hr' hne
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro e he
    by_cases hexp : kwGraphLoopExponent G e = ons_finsetExponent S
    · exfalso
      have hdegree' := kwGraphLoopExponent_totalDegree G e
      rw [hexp, hdegree] at hdegree'
      omega
    · simp [hexp]
  · intro hnot
    exact (hnot hrange).elim

theorem kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) (r : ℕ)
    (d : Fin (r + 1) → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) = 1 := by
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_straightLine
    G embedding hdeg S r d hd, hscalar]
  ring

theorem kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    (S : Finset (Sym2 V)) {n : ℕ} [NeZero n]
    (d : Fin n → G.Dart)
    (hd : d ∈ kwGraphSquarefreeLoopFinset G embedding.turnPhase S)
    (hscalar : kwGraphLoopScalar G embedding.turnPhase d = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
        (ons_finsetExponent S) = 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one
    G embedding hdeg S r d hd hscalar


end StatMech.FrontierA
