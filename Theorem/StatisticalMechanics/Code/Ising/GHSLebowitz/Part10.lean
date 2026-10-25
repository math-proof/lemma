/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part9
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsLOutFieldWeight_split (β h : ℝ) (q a : ConfigSpace V) :
    ghsLOutFieldWeight β h q a =
      ghsLOutFieldWeight β h q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsLOutFieldWeight
  congr 2
  apply Finset.sum_congr rfl
  intro v hv
  have hq : ¬ q v = true := by
    simpa using (Finset.mem_compl.mp hv)
  unfold spin
  rw [ghsLUComplete_eq_on q a hq]


theorem ghsL_wJ_field_eq_tWeight_mul_out (β h : ℝ) (q a : ConfigSpace V) :
    Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) a =
      ghsLTWeight G β h q a * ghsLOutFieldWeight β h q a := by
  unfold Sharpness.wJ ghsLTWeight ghsLOutFieldWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : (∑ v : V, spin a v) =
      (∑ v ∈ ghsLAgreeFinset q, spin a v) +
        ∑ v ∈ (ghsLAgreeFinset q)ᶜ, spin a v := by
    calc
      (∑ v : V, spin a v) = ∑ v ∈ ghsLAgreeFinset q ∪ (ghsLAgreeFinset q)ᶜ,
          spin a v := by rw [Finset.union_compl]
      _ = _ := Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro v hvA hvAc
        exact (Finset.mem_compl.mp hvAc) hvA)
  rw [show (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
      (fun _ => 2 * β) e * bond a e) =
      2 * β * ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e by
        rw [Finset.mul_sum]]
  rw [show (∑ x : V, (fun _ => 2 * β * h) x * spin a x) =
      2 * β * h * ∑ x : V, spin a x by rw [Finset.mul_sum]]
  rw [hsplit]
  ring


theorem ghsLFibreT_eq_agreementMag (β h : ℝ) (y : V) (q : ConfigSpace V) :
    ghsLFibreT G β h y q =
      ghsvp_agreementMag G β h y (ghsLAgreeFinset q) := by
  rw [ghsLFibreT_eq_tExpectation]
  by_cases hy : y ∈ ghsLAgreeFinset q
  · have hqy : q y = true := (mem_ghsLAgreeFinset q y).mp hy
    unfold ghsvp_agreementMag ghsvp_vertexCorrField Sharpness.expJ
    rw [if_pos hy]
    let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      ghsLTWeight G β h q (ghsLTComplete q st)
    let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      spin (ghsLTComplete q st) y
    let gO : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
      ghsLOutFieldWeight β h q (ghsLUComplete q su)
    have htvar (a : ConfigSpace V) : tvar a (ghsLMate q a) y = spin a y := by
      rw [ghsL_tvar_mate, if_pos hqy]
    have htlocal (a : ConfigSpace V) : spin a y = tObs (ghsLSplitEquiv q a).1 := by
      unfold tObs spin
      rw [ghsLTComplete_eq_on q a hqy]
    have hbase (a : ConfigSpace V) : ghsLTWeight G β h q a =
        fT (ghsLSplitEquiv q a).1 := by
      rw [ghsLTWeight_split]
    have hout (a : ConfigSpace V) : ghsLOutFieldWeight β h q a =
        gO (ghsLSplitEquiv q a).2 := by
      rw [ghsLOutFieldWeight_split]
    have hcross := ghsL_split_cross_product (V := V) q
      (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) gO
    unfold ghsLTExpectation
    have hzt : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) ≠ 0 :=
      (Finset.sum_pos (fun a _ => ghsLTWeight_pos G β h q a) Finset.univ_nonempty).ne'
    have hza : Sharpness.ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) ≠ 0 :=
      (Sharpness.ZJ_pos _ _ _).ne'
    field_simp [hzt, hza]
    have hL1 : (∑ a : ConfigSpace V,
        ghsLTWeight G β h q a * tvar a (ghsLMate q a) y) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase, htvar, htlocal]
      ring
    have hL0 : (∑ a : ConfigSpace V, ghsLTWeight G β h q a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase]
      ring
    have hR1 : (∑ a : ConfigSpace V, spinProd {y} a *
        Sharpness.wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun _ => 2 * β) (fun _ => 2 * β * h) a) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
            gO (ghsLSplitEquiv q a).2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsL_wJ_field_eq_tWeight_mul_out, hbase, hout]
      simp only [spinProd, Finset.prod_singleton]
      rw [htlocal]
      ring
    have hR0 : Sharpness.ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun _ => 2 * β) (fun _ => 2 * β * h) =
        ∑ a : ConfigSpace V,
          fT (ghsLSplitEquiv q a).1 * gO (ghsLSplitEquiv q a).2 := by
      unfold Sharpness.ZJ
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsL_wJ_field_eq_tWeight_mul_out, hbase, hout]
    rw [hL1, hL0, hR1, hR0]
    simpa [mul_comm] using hcross
  · have hqy : ¬ q y = true := fun h => hy ((mem_ghsLAgreeFinset q y).mpr h)
    unfold ghsvp_agreementMag ghsLTExpectation
    rw [if_neg hy]
    simp_rw [ghsL_tvar_mate, if_neg hqy, mul_zero]
    simp


end Ising
end StatMech
