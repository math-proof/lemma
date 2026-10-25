/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part4
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shk_restrictedSusceptibility_le (p : ℝ≥0) (hp : p ≤ 1)
    (S Lam : Finset (Site d)) (h0S : origin d ∈ S) (h0Lam : origin d ∈ Lam)
    (hphi : phi d p hp S < 1) :
    shk_restrictedSusceptibility p hp Lam (origin d) ≤
      (S.card : ℝ) / (1 - phi d p hp S) := by
  classical
  let chi : Site d → ℝ := fun u => shk_restrictedSusceptibility p hp Lam u
  obtain ⟨u, huLam, humax⟩ := Finset.exists_max_image Lam chi ⟨origin d, h0Lam⟩
  let g : Multiplicative (Site d) := Multiplicative.ofAdd u
  have hgu : g • origin d = u := by
    funext i
    simp [g, smul_site_apply, origin]
  let Su := shk_translateFinset g S
  have huSu : u ∈ Su := by
    rw [← hgu]
    exact (shk_mem_translateFinset_smul g S (origin d)).2 h0S
  let Sin := Lam ∩ Su
  let bnd := boundaryEdges d Su
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let q : Site d → ℝ := fun x =>
    mu.real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x})
  let q' : Site d → Site d → ℝ := fun b x =>
    mu.real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) b {x})
  let cw : Site d × Site d → ℝ := fun e =>
    mu.real (connEvent (hypercubicLattice d) (Su : Set (Site d)) u {e.1})
  have hcont : ∀ b : Site d, ∑ x ∈ Lam, q' b x ≤ chi u := by
    intro b
    by_cases hb : b ∈ Lam
    · exact humax b hb
    · have hz : ∀ x ∈ Lam, q' b x = 0 := by
        intro x _
        simp only [q', connEvent, ConnToSet]
        have hempty : {omega : ConfigSpace (Sym2 (Site d)) |
            ∃ (_ : b ∈ (Lam : Set (Site d))) (z : Site d)
              (_ : z ∈ (Lam : Set (Site d))), z ∈ ({x} : Set (Site d)) ∧
                ConnWithin (hypercubicLattice d) omega (Lam : Set (Site d))
                  ⟨b, by assumption⟩ ⟨z, by assumption⟩} = ∅ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hb', _⟩
          exact hb (by simpa using hb')
        rw [hempty]
        exact measureReal_empty
      calc
        (∑ x ∈ Lam, q' b x) = 0 := Finset.sum_eq_zero fun x hx => hz x hx
        _ ≤ chi u := by
          simp only [chi, shk_restrictedSusceptibility]
          exact Finset.sum_nonneg fun x _ => measureReal_nonneg
  have hfe : ∀ x ∈ Lam, x ∉ Sin →
      q x ≤ ∑ e ∈ bnd, ((p : ℝ) * cw e) * q' e.2 x := by
    intro x hxLam hxSin
    have hxSu : x ∉ Su := by
      intro hx
      exact hxSin (Finset.mem_inter.mpr ⟨hxLam, hx⟩)
    have hb := bk_criterion_infinite_lattice_singleton p hp Lam Su u x huSu hxSu
    simpa only [q, q', cw, bnd, mul_assoc] using hb
  have hselfSin : chi u ≤ (Sin.card : ℝ) + phi d p hp S * chi u := by
    apply susceptibility_self_consistent Lam Sin Finset.inter_subset_left bnd
      (fun e => e.2) (p : ℝ) p.coe_nonneg cw q q'
      (fun _ _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      (fun x _ => measureReal_le_one) hfe (chi u)
    · rfl
    · exact hcont
    · have hcoeff := shk_phi_translate p hp g S h0S
      rw [hgu] at hcoeff
      simpa only [Su, bnd, cw,
        shk_connEvent_singleton_eq_connWithinEvent] using hcoeff.symm
  have hcard : (Sin.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast le_trans (Finset.card_le_card Finset.inter_subset_right)
      (le_of_eq (shk_translateFinset_card g S))
  have hself : chi u ≤ (S.card : ℝ) + phi d p hp S * chi u :=
    hselfSin.trans (add_le_add hcard le_rfl)
  have hchi0 : 0 ≤ chi u := Finset.sum_nonneg fun x _ => measureReal_nonneg
  have hub := (susceptibility_finite_of_self_consistent
    (chi u) (S.card : ℝ) (phi d p hp S) hchi0 hphi hself).2
  exact (humax (origin d) h0Lam).trans hub


theorem shk_connWithinProb_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) (S : Finset (Site d)) (x : Site d) :
    connWithinProb d p hp S x ≤ connWithinProb d q hq S x := by
  classical
  by_cases h0 : origin d ∈ S
  · by_cases hx : x ∈ S
    · have hm := ibk_measure_mono_parameter hp hq hpq
        (internalEdgesFinset S)
        (shk_connEvent_singleton_dependsOn S (origin d) x)
        (isIncreasing_connEvent (hypercubicLattice d) (S : Set (Site d))
          (origin d) {x})
      rw [shk_connEvent_singleton_eq_connWithinEvent] at hm
      have hpbook := connWithinProb_eq p hp S x (by simpa using h0) (by simpa using hx)
      have hqbook := connWithinProb_eq q hq S x (by simpa using h0) (by simpa using hx)
      rw [hpbook, hqbook]
      simpa only [withinConnEvent, connWithinEvent] using hm
    · unfold connWithinProb
      rw [dif_pos h0, dif_neg hx, dif_pos h0, dif_neg hx]
  · unfold connWithinProb
    rw [dif_neg h0, dif_neg h0]


theorem shk_phi_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) (S : Finset (Site d)) :
    phi d p hp S ≤ phi d q hq S := by
  unfold phi
  have hsum : (∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1) ≤
      ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 := by
    exact Finset.sum_le_sum fun e _ => shk_connWithinProb_mono hp hq hpq S e.1
  have hsum0 : 0 ≤ ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
    Finset.sum_nonneg fun e _ => connWithinProb_nonneg d q hq S e.1
  calc
    (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1 ≤
        (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
      mul_le_mul_of_nonneg_left hsum p.coe_nonneg
    _ ≤ (q : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hpq) hsum0


theorem bondParam_mono : Monotone bondParam := by
  intro beta gamma hbg
  unfold bondParam
  apply Real.toNNReal_le_toNNReal
  have hexp : Real.exp (-gamma) ≤ Real.exp (-beta) :=
    Real.exp_le_exp.mpr (neg_le_neg hbg)
  linarith


theorem exists_phiBeta_witness_of_lt_tildeBetaCPerco {beta : ℝ}
    (hbeta : beta < tildeBetaCPerco d) :
    ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d beta S < 1 := by
  unfold tildeBetaCPerco at hbeta
  have hne : (tildeBetaCPercoSet d).Nonempty := by
    refine ⟨0, le_rfl, {origin d}, by simp, ?_⟩
    simp [phiBeta, bondParam, phi]
  obtain ⟨gamma, hgamma, hbg⟩ := exists_lt_of_lt_csSup hne hbeta
  obtain ⟨hgamma0, S, h0S, hphi⟩ := hgamma
  refine ⟨S, h0S, ?_⟩
  unfold phiBeta at hphi ⊢
  exact (shk_phi_mono (bondParam_le_one beta) (bondParam_le_one gamma)
    (bondParam_mono hbg.le) S).trans_lt hphi


end Sharpness
end StatMech
