/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem abbl_residual_activeGhost_card {d n : Nat} (hn : 0 < n)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (hres : abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta ∈
      abblResidualEvent d n) :
    n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n)
      (sctBoxOrigin d n) eta).card := by
  let omega := abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta
  obtain ⟨hmix, hnot⟩ := hres
  obtain ⟨_, z, _, hzTarget, hconn⟩ := hmix
  rcases hzTarget with rfl | ⟨y, hzy, hybdry⟩
  · exact False.elim (hnot ⟨Set.mem_univ _, none, Set.mem_univ _, rfl, hconn⟩)
  · subst z
    have hphys : omega ∈ connEvent (withGhost (sctBoxGraph d n))
        Set.univ (some (sctBoxOrigin d n)) {some y} :=
      ⟨Set.mem_univ _, some y, Set.mem_univ _, rfl, hconn⟩
    have hclosed := abbl_closeGhost_conn_of_not_ghost
      (sctBoxGraph d n) (sctBoxOrigin d n) y omega hphys hnot
    exact abbl_activeGhost_card_ge_of_boundary hn eta gamma y hybdry hclosed


theorem abbl_residual_prob_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (abblResidualEvent d n) ≤
      Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  apply abbl_residual_le_exp (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) beta h hJ hbeta hh (n + 1)
    (abblResidualEvent d n)
  · intro omega hres
    exact hres.2
  · intro eta gamma hres
    exact abbl_residual_activeGhost_card hn eta gamma hres


theorem abbl_abfaMag_le_abbMag_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h ≤ abbMag d n beta h ∧
      abbMag d n beta h ≤
        abfaMag (sctBoxGraph d n) (abbCoupling d n)
          (sctBoxOrigin d n) beta h +
            Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  let A := connEvent (withGhost (sctBoxGraph d n)) Set.univ
    (some (sctBoxOrigin d n)) (abbTarget d n)
  let B := connEvent (withGhost (sctBoxGraph d n)) Set.univ
    (some (sctBoxOrigin d n)) {none}
  let R := abblResidualEvent d n
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem (sctBoxGraph d n) (abbCoupling d n) hJ
      beta h hbeta hh
  have hBA : B ⊆ A := by
    intro omega hconn
    rcases hconn with ⟨ho, z, hz, rfl, hc⟩
    exact ⟨ho, none, hz, none_mem_abbTarget d n, hc⟩
  have hAunion : A ⊆ B ∪ R := by
    intro omega hA
    by_cases hB : omega ∈ B
    · exact Or.inl hB
    · exact Or.inr ⟨hA, hB⟩
  constructor
  · change probV p B ≤ probV p A
    exact abgi_probV_mono p hp hBA
  · change probV p A ≤ probV p B + _
    calc
      probV p A ≤ probV p (B ∪ R) := abgi_probV_mono p hp hAunion
      _ ≤ probV p B + probV p R := abgi_probV_union_le p hp B R
      _ ≤ probV p B + Real.exp (-(h * ((n + 1 : Nat) : Real))) :=
        by
          simpa only [p, R] using
            add_le_add (le_refl (probV p B))
              (abbl_residual_prob_le (d := d) hn beta h hbeta hh)


theorem abbl_abfaMag_relabel {U W : Type*}
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (sigma : U ≃ W)
    (hgraph : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (J : Sym2 U → Real) (K : Sym2 W → Real)
    (hcoupling : ∀ x y, G.Adj x y →
      J s(x, y) = K s(sigma x, sigma y))
    (o : U) (beta h : Real) :
    abfaMag G J o beta h = abfaMag H K (sigma o) beta h := by
  let tau : Option U ≃ Option W := sigma.optionCongr
  have htau : ∀ a b, (withGhost G).Adj a b ↔
      (withGhost H).Adj (tau a) (tau b) := by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;>
      simp [tau, withGhost, hgraph]
  unfold abfaMag
  rw [abb_probV_connEvent_relabel (withGhost G) (withGhost H) tau htau
    (abfaParams G J beta h) (some o) none]
  congr 1
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [abbl_abbEdgeEquiv_symm_mk]
      rcases a with _ | a <;> rcases b with _ | b
      · change abfaParams G J beta h s(none, none) =
          abfaParams H K beta h s(none, none)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
          FieldGhostDict.ghostCoupling, pBeta]
      · change abfaParams G J beta h s(none, some (sigma.symm b)) =
          abfaParams H K beta h s(none, some b)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges]
      · change abfaParams G J beta h s(some (sigma.symm a), none) =
          abfaParams H K beta h s(some a, none)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges]
      · change abfaParams G J beta h
          s(some (sigma.symm a), some (sigma.symm b)) =
            abfaParams H K beta h s(some a, some b)
        simp only [abfaParams, abpdBetaFieldParams, paramOn]
        have hghostU : s(some (sigma.symm a), some (sigma.symm b)) ∉
            FieldGhostDict.ghostEdges U := by
          simp [FieldGhostDict.ghostEdges]
        have hghostW : s(some a, some b) ∉
            FieldGhostDict.ghostEdges W := by
          simp [FieldGhostDict.ghostEdges]
        rw [if_neg hghostU, if_neg hghostW,
          abfaLiftCoupling_some_some, abfaLiftCoupling_some_some]
        by_cases hab : G.Adj (sigma.symm a) (sigma.symm b)
        · have hab' : H.Adj a b := by
            simpa using (hgraph (sigma.symm a) (sigma.symm b)).mp hab
          rw [if_pos (SimpleGraph.mem_edgeFinset.mpr hab),
            if_pos (SimpleGraph.mem_edgeFinset.mpr hab')]
          have hc : J s(sigma.symm a, sigma.symm b) = K s(a, b) := by
            simpa using hcoupling (sigma.symm a) (sigma.symm b) hab
          exact congrArg (fun t ↦ pBeta t beta) hc
        · have hab' : ¬ H.Adj a b := fun hw ↦
            hab ((hgraph (sigma.symm a) (sigma.symm b)).mpr (by simpa using hw))
          rw [if_neg (fun he ↦ hab (SimpleGraph.mem_edgeFinset.mp he)),
            if_neg (fun he ↦ hab' (SimpleGraph.mem_edgeFinset.mp he))]


end Sharpness
end StatMech
