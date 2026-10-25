/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part11
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_sum_countEq_eq_countP {A : Type*} [DecidableEq A]
    (F : Finset A) (l : List A) :
    (∑ e ∈ F, l.countP (fun a => decide (a = e))) =
      l.countP (fun a => decide (a ∈ F)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ F <;> simp [ha]

theorem ons_plusRectPathDefectSign_cut (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) =
      (-1 : Real) ^ path.edges.countP (fun primal =>
        decide (primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩)) := by
  unfold ons_plusRectPathDefectSign ons_plusRectCutEven
  change (∏ edge ∈ ons_plusRectDualCut n config,
      ons_plusRectPathEdgeSign n path edge) = _
  rw [ons_plusRectDualCut, Finset.prod_map]
  calc
    (∏ typed ∈ multibondCut (ons_plusWiredBondEnds 2 n) config.1,
        ons_plusRectPathEdgeSign n path
          (ons_touchingBondToRectEdge n typed)) =
        ∏ typed ∈ multibondCut (ons_plusWiredBondEnds 2 n) config.1,
          (-1 : Real) ^ path.edges.countP
            (fun primal => decide (primal = typed.1)) := by
      apply Finset.prod_congr rfl
      intro typed _
      unfold ons_plusRectPathEdgeSign
      split
      · have hedgeEq :
            (⟨ons_touchingBondToRectEdge n typed, ‹_›⟩ :
              {edge // edge ∈
                (ons_rectDualGraph (2 * n + 1)
                  (2 * n + 1)).edgeFinset}) =
              ons_touchingBondEquivRectDualEdge n typed :=
          Subtype.ext rfl
        rw [hedgeEq, (ons_touchingBondEquivRectDualEdge n).symm_apply_apply]
      · exact False.elim (by
          apply ‹ons_touchingBondToRectEdge n typed ∉ _›
          exact (ons_touchingBondEquivRectDualEdge n typed).2)
    _ = ∏ primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩,
        (-1 : Real) ^ path.edges.countP
          (fun edge => decide (edge = primal)) := by
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro typed _
      rfl
    _ = (-1 : Real) ^
        (∑ primal ∈
          (multibondCut (ons_plusWiredBondEnds 2 n) config.1).map
            ⟨Subtype.val, Subtype.val_injective⟩,
          path.edges.countP (fun edge => decide (edge = primal))) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      congr 1
      exact ons_sum_countEq_eq_countP _ path.edges

theorem ons_plusPath_crossCount_eq_wiredCutLattice (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    kwd_crossCount (kwd_sideBoundary (glue (plusField 2) tau)) path =
      path.edges.countP (fun edge =>
        decide (edge ∈ ons_plusWiredCutLattice 2 n tau)) := by
  unfold kwd_crossCount
  apply List.countP_congr
  intro edge hedge
  induction edge using Sym2.inductionOn with
  | _ x y =>
      have hadj : (hypercubicLattice 2).Adj x y :=
        path.adj_of_mem_edges hedge
      let config := glue (plusField 2) tau
      have htouch (hne : config x ≠ config y) :
          x ∈ box 2 n ∨ y ∈ box 2 n := by
        by_contra hnot
        push Not at hnot
        have hx : config x = true := by
          change glue (plusField 2) tau x = true
          rw [glue_not_mem _ _ hnot.1]
          rfl
        have hy : config y = true := by
          change glue (plusField 2) tau y = true
          rw [glue_not_mem _ _ hnot.2]
          rfl
        exact hne (hx.trans hy.symm)
      have hmem : s(x, y) ∈
          ons_fvCutEdges (bondFinsetTouch 2 n) config ↔
          config x ≠ config y := by
        unfold ons_fvCutEdges
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨_, hneg⟩
          exact (kwg_isSplit_mk config x y).mp
            ((kwg_isSplit_iff_bond_neg config s(x, y)).mpr hneg)
        · intro hne
          refine ⟨mk_mem_bondFinsetTouch hadj (htouch hne), ?_⟩
          exact (kwg_isSplit_iff_bond_neg config s(x, y)).mp
            ((kwg_isSplit_mk config x y).mpr hne)
      rw [ons_plusWiredCutLattice_eq_fvCutEdges]
      change kwd_sideBoundary config s(x, y) = true ↔ decide
        (s(x, y) ∈ ons_fvCutEdges (bondFinsetTouch 2 n) config) = true
      have hdecide : decide
          (s(x, y) ∈ ons_fvCutEdges (bondFinsetTouch 2 n) config) =
          decide (config x ≠ config y) := decide_eq_decide.mpr hmem
      rw [kwd_sideBoundary_mk, hdecide]
      cases config x <;> cases config y <;> rfl


theorem ons_plusRectPathDefectSign_optionAnchoredEquiv (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusRectPathDefectSign n path
        (ons_plusRectCutEven n (ons_optionAnchoredEquiv tau)) =
      ons_plusWiredEndpointSign 2 n
        (ons_optionAnchoredEquiv tau).1 u v := by
  rw [ons_plusRectPathDefectSign_cut]
  change (-1 : Real) ^ path.edges.countP (fun primal =>
      decide (primal ∈ ons_plusWiredCutLattice 2 n tau)) = _
  rw [← ons_plusPath_crossCount_eq_wiredCutLattice n tau path]
  rw [ons_plusWiredEndpointSign_eq_pathSign 2 n tau path]
  unfold ons_plusLowTempPathSign
  exact (neg_one_pow_eq_ite : (-1 : Real) ^ _ = _)


theorem ons_plusRectPathDefectSign_eq_endpointSign (n : Nat)
    (F : ons_PlusRectEvenSubgraph n) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) :
    ons_plusRectPathDefectSign n path F =
      ons_plusWiredEndpointSign 2 n
        ((ons_plusRectCutEvenEquiv n).symm F).1 u v := by
  let config := (ons_plusRectCutEvenEquiv n).symm F
  let tau := (ons_optionAnchoredEquiv
    (I := {x // x ∈ box 2 n})).symm config
  have hconfig : ons_optionAnchoredEquiv tau = config :=
    (ons_optionAnchoredEquiv
      (I := {x // x ∈ box 2 n})).apply_symm_apply config
  have hF : ons_plusRectCutEven n config = F :=
    (ons_plusRectCutEvenEquiv n).apply_symm_apply F
  calc
    ons_plusRectPathDefectSign n path F =
        ons_plusRectPathDefectSign n path (ons_plusRectCutEven n config) :=
      congrArg (ons_plusRectPathDefectSign n path) hF.symm
    _ = ons_plusWiredEndpointSign 2 n
        (ons_optionAnchoredEquiv tau).1 u v :=
      by
        rw [← hconfig]
        exact ons_plusRectPathDefectSign_optionAnchoredEquiv n tau path
    _ = ons_plusWiredEndpointSign 2 n config.1 u v := by rw [hconfig]
    _ = ons_plusWiredEndpointSign 2 n
        ((ons_plusRectCutEvenEquiv n).symm F).1 u v := by rfl

end
end StatMech.Onsager
