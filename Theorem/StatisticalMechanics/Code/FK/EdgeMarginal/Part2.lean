/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Def.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
open scoped BigOperators
open SimpleGraph


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] [DecidableRel G.Adj] in


theorem numClustersBC_antitone (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G C' ω ≤ numClustersBC G C ω := by
  unfold numClustersBC
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (sup_le_sup_left hCC' (openSub G ω))

omit [DecidableEq V] in


theorem bcWeight_antitone (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (ω : ConfigSpace (Sym2 V)) :
    bcWeight G C' p q ω ≤ bcWeight G C p q ω := by
  unfold bcWeight
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hq (numClustersBC_antitone G C C' hCC' ω))
    (edgeProduct_pos G hp hp1 ω).le

omit [DecidableEq V] in


theorem bcWeight_qpow_le (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (N : ℕ) (ω : ConfigSpace (Sym2 V))
    (hb : numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
    bcWeight G C p q ω ≤ q ^ N * bcWeight G C' p q ω := by
  unfold bcWeight
  have hpow : q ^ numClustersBC G C ω ≤ q ^ (numClustersBC G C' ω + N) :=
    pow_le_pow_right₀ hq hb
  rw [pow_add] at hpow
  have hep := (edgeProduct_pos G hp hp1 ω).le
  calc edgeProduct G p ω * q ^ numClustersBC G C ω
      ≤ edgeProduct G p ω * (q ^ numClustersBC G C' ω * q ^ N) :=
        mul_le_mul_of_nonneg_left hpow hep
    _ = q ^ N * (edgeProduct G p ω * q ^ numClustersBC G C' ω) := by ring


theorem bcZ_qpow_le (C C' : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel C'.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (N : ℕ)
    (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
    bcZ G C p q ≤ q ^ N * bcZ G C' p q := by
  unfold bcZ
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun ω _ => bcWeight_qpow_le G C C' hp hp1 hq N ω (hb ω)

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma div_le_qpow_div {Nw Nf Zc Zc' qN : ℝ} (hNum : Nw ≤ Nf)
    (hNumnn : 0 ≤ Nf) (hZc : 0 < Zc) (hZc' : 0 < Zc')
    (hZbound : Zc ≤ qN * Zc') : Nw / Zc' ≤ qN * (Nf / Zc) := by
  have hrhs : qN * (Nf / Zc) = (qN * Nf) / Zc := by ring
  rw [hrhs, div_le_div_iff₀ hZc' hZc]
  calc Nw * Zc ≤ Nf * Zc := mul_le_mul_of_nonneg_right hNum hZc.le
    _ ≤ Nf * (qN * Zc') := mul_le_mul_of_nonneg_left hZbound hNumnn
    _ = qN * Nf * Zc' := by ring


theorem bcEventMass_le_qpow (C C' : SimpleGraph V) [DecidableRel C.Adj]
    [DecidableRel C'.Adj] (hCC' : C ≤ C') {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (N : ℕ) (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N)
    {A : Set (ConfigSpace (Sym2 V))} (hA0 : ∀ ω, 0 ≤ A.indicator (fun _ => (1 : ℝ)) ω) :
    bcEventMass G C' p q A ≤ q ^ N * bcEventMass G C p q A := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ : 0 < bcZ G C p q := bcZ_pos G C hp hp1 hq0
  have hZ' : 0 < bcZ G C' p q := bcZ_pos G C' hp hp1 hq0
  set Nw := ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcWeight G C' p q ω
    with hNw
  set Nf := ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcWeight G C p q ω
    with hNf
  have hNum : Nw ≤ Nf := Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (bcWeight_antitone G C C' hCC' hp hp1 hq ω) (hA0 ω)
  have hNumnn : 0 ≤ Nf := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (hA0 ω) (bcWeight_nonneg G C hp hp1 hq0 ω)
  have hZbound : bcZ G C p q ≤ q ^ N * bcZ G C' p q := bcZ_qpow_le G C C' hp hp1 hq N hb
  have hEM' : bcEventMass G C' p q A = Nw / bcZ G C' p q := by
    unfold bcEventMass bcProb
    rw [hNw, Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [mul_div_assoc]
  have hEM : bcEventMass G C p q A = Nf / bcZ G C p q := by
    unfold bcEventMass bcProb
    rw [hNf, Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [mul_div_assoc]
  rw [hEM', hEM]
  exact div_le_qpow_div hNum hNumnn hZ hZ' hZbound


omit [DecidableEq V] [DecidableRel G.Adj] in


theorem card_connectedComponent_le_sup_fromEdgeSet (S : Finset (Sym2 V)) :
    ∀ A : SimpleGraph V,
      Nat.card A.ConnectedComponent
        ≤ Nat.card (A ⊔ fromEdgeSet (↑S)).ConnectedComponent + S.card := by
  classical
  induction S using Finset.induction with
  | empty => intro A; simp
  | insert e S he ih =>
    intro A
    have key : A ⊔ fromEdgeSet (↑(insert e S))
        = (A ⊔ fromEdgeSet (↑S)) ⊔ fromEdgeSet {e} := by
      rw [Finset.coe_insert, Set.insert_eq, fromEdgeSet_union, sup_comm (fromEdgeSet {e}),
        ← sup_assoc]
    obtain ⟨x, y, hxy⟩ : ∃ x y : V, fromEdgeSet ({e} : Set (Sym2 V)) = edge x y := by
      induction e using Sym2.ind with | _ x y => exact ⟨x, y, by rw [edge]⟩
    rw [key, hxy]
    have h1 := ih A
    have h2 := card_connectedComponent_le_sup_edge (A ⊔ fromEdgeSet (↑S)) x y
    rw [Finset.card_insert_of_notMem he]
    omega

omit [DecidableEq V] [DecidableRel G.Adj] in


theorem numClustersBC_bot_le (C' : SimpleGraph V) [DecidableRel C'.Adj]
    (ω : ConfigSpace (Sym2 V)) :
    numClustersBC G (⊥ : SimpleGraph V) ω ≤ numClustersBC G C' ω + C'.edgeFinset.card := by
  unfold numClustersBC
  rw [sup_bot_eq]
  have h := card_connectedComponent_le_sup_fromEdgeSet (V := V) C'.edgeFinset (openSub G ω)
  rwa [coe_edgeFinset, fromEdgeSet_edgeSet] at h

end FK
end StatMech
