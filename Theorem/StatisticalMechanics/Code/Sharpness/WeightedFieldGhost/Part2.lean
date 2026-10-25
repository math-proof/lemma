/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part4
import Def.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace WeightedFieldGhost

open StatMech.Ising

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum endsM)

open StatMech.Sharpness.RandomCurrent (connK)

open StatMech.Sharpness.HcovAssembly


theorem odd_source_card (o x y : V) (hxy : x ≠ y) :
    Odd ((({o} : Finset V) ∆ {x, y}).card) := by
  by_cases hox : o = x
  · subst x
    have heq : ({o} : Finset V) ∆ {o, y} = {y} := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq]
    simp
  · by_cases hoy : o = y
    · subst y
      have heq : ({o} : Finset V) ∆ {x, o} = {x} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq]
      simp
    · have heq : ({o} : Finset V) ∆ {x, y} = {o, x, y} := by
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        aesop
      rw [heq, Finset.card_insert_of_notMem (by simp [hox, hoy]),
        Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
      decide

theorem even_field_source_card (o z : V) :
    Even ((({o} : Finset V) ∆ {z}).card) := by
  by_cases hoz : o = z
  · subst z
    simp
  · have heq : ({o} : Finset V) ∆ {z} = {o, z} := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      aesop
    rw [heq, Finset.card_insert_of_notMem (by simp [hoz]), Finset.card_singleton]
    decide

theorem weightedBond_covariance_sourcePair (β h : ℝ) (J : Sym2 V -> ℝ)
    (o x y : V) (hxy : x ≠ y) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {x, y})) -
          weightedExpectation G β J h (spinProd ({x, y} : Finset V)) *
            weightedExpectation G β J h (spinProd ({o} : Finset V))) =
      weightedBondDelta G β h J o s(x, y) := by
  let S : Finset V := ({o} : Finset V) ∆ {x, y}
  let A : Finset (Option V) := insert none (S.map someEmb)
  have hSodd : Odd S.card := odd_source_card o x y hxy
  have hpair : Even (({x, y} : Finset V).card) := by
    rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
    decide
  have hsingle : Odd (({o} : Finset V).card) := by simp
  have hrepS := weightedExpectation_eq_currentRatio_odd G β h J S hSodd
  have hrepPair := weightedExpectation_eq_currentRatio_even G β h J
    ({x, y} : Finset V) hpair
  have hrepO := weightedExpectation_eq_currentRatio_odd G β h J
    ({o} : Finset V) hsingle
  have hdiff : A ∆ {some o, none} = ({x, y} : Finset V).map someEmb := by
    ext z
    cases z with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some w =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or, exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext z
    simp [someEmb]
    aesop
  change weightedExpectation G β J h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β J) A /
      currentSum (withGhost G) β (ghostCoupling h β J) ∅ at hrepS
  rw [← hdiff] at hrepPair
  rw [← hpairSource] at hrepO
  have hZne : currentSum (withGhost G) β (ghostCoupling h β J) ∅ ≠ 0 :=
    ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β J) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅)
    (weightedExpectation G β J h (spinProd S))
    (weightedExpectation G β J h (spinProd ({x, y} : Finset V)))
    (weightedExpectation G β J h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepPair hrepO
  simpa [weightedBondDelta, hcaBondSource, A, S] using hgcr

theorem weightedField_covariance_sourcePair (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (spinProd (({o} : Finset V) ∆ {z})) -
          weightedExpectation G β J h (spinProd ({z} : Finset V)) *
            weightedExpectation G β J h (spinProd ({o} : Finset V))) =
      weightedFieldDelta G β h J o z := by
  let S : Finset V := ({o} : Finset V) ∆ {z}
  let A : Finset (Option V) := S.map someEmb
  have hSeven : Even S.card := even_field_source_card o z
  have hzodd : Odd (({z} : Finset V).card) := by simp
  have hood : Odd (({o} : Finset V).card) := by simp
  have hrepS := weightedExpectation_eq_currentRatio_even G β h J S hSeven
  have hrepZ := weightedExpectation_eq_currentRatio_odd G β h J ({z} : Finset V) hzodd
  have hrepO := weightedExpectation_eq_currentRatio_odd G β h J ({o} : Finset V) hood
  have hdiff : A ∆ {some o, none} = insert none (({z} : Finset V).map someEmb) := by
    ext w
    cases w with
    | none => simp [A, Finset.mem_symmDiff, someEmb]
    | some v =>
        simp only [A, S, Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_map, someEmb_apply,
          Option.some.injEq, Option.some_ne_none, false_or, exists_eq_right]
        tauto
  have hpairSource : ({some o, none} : Finset (Option V)) =
      insert none (({o} : Finset V).map someEmb) := by
    ext w
    simp [someEmb]
    aesop
  change weightedExpectation G β J h (spinProd S) =
    currentSum (withGhost G) β (ghostCoupling h β J) A /
      currentSum (withGhost G) β (ghostCoupling h β J) ∅ at hrepS
  rw [← hdiff] at hrepZ
  rw [← hpairSource] at hrepO
  have hZne : currentSum (withGhost G) β (ghostCoupling h β J) ∅ ≠ 0 :=
    ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hgcr := GhostCurrentRep.gcr_ghostCurrentRep (withGhost G) β
    (ghostCoupling h β J) A (by simp)
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅)
    (weightedExpectation G β J h (spinProd S))
    (weightedExpectation G β J h (spinProd ({z} : Finset V)))
    (weightedExpectation G β J h (spinProd ({o} : Finset V)))
    rfl hZne hrepS hrepZ hrepO
  simpa [weightedFieldDelta, hcaFieldSource, A, S] using hgcr

theorem weighted_spin_mul_bond (o x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => spin s o * bond s s(x, y)) =
      spinProd (({o} : Finset V) ∆ {x, y}) := by
  funext s
  rw [show spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show bond s s(x, y) = spinProd ({x, y} : Finset V) s by
      rw [bond_mk, spinProd, Finset.prod_pair hxy], spinProd_mul_self]

theorem weighted_bond_pair (x y : V) (hxy : x ≠ y) :
    (fun s : ConfigSpace V => bond s s(x, y)) = spinProd ({x, y} : Finset V) := by
  funext s
  rw [bond_mk, spinProd, Finset.prod_pair hxy]

theorem weighted_spin_mul_spin (o z : V) :
    (fun s : ConfigSpace V => spin s o * spin s z) =
      spinProd (({o} : Finset V) ∆ {z}) := by
  funext s
  rw [show spin s o = spinProd ({o} : Finset V) s by simp [spinProd],
    show spin s z = spinProd ({z} : Finset V) s by simp [spinProd], spinProd_mul_self]

theorem weighted_spin_single (z : V) :
    (fun s : ConfigSpace V => spin s z) = spinProd ({z} : Finset V) := by
  funext s
  simp [spinProd]

theorem weightedBond_covariance_eq_delta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o : V) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (fun s => spin s o * bond s e) -
          weightedExpectation G β J h (fun s => spin s o) *
            weightedExpectation G β J h (fun s => bond s e)) =
      weightedBondDelta G β h J o e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : G.Adj x y := by simpa using (SimpleGraph.mem_edgeFinset.mp he)
      have hxy := G.ne_of_adj hadj
      rw [weighted_spin_mul_bond o x y hxy, weighted_bond_pair x y hxy,
        weighted_spin_single o, mul_comm
          (weightedExpectation G β J h (spinProd ({o} : Finset V)))]
      exact weightedBond_covariance_sourcePair G β h J o x y hxy

theorem weightedField_covariance_eq_delta (β h : ℝ) (J : Sym2 V -> ℝ)
    (o z : V) :
    (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2 *
        (weightedExpectation G β J h (fun s => spin s o * spin s z) -
          weightedExpectation G β J h (fun s => spin s o) *
            weightedExpectation G β J h (fun s => spin s z)) =
      weightedFieldDelta G β h J o z := by
  rw [weighted_spin_mul_spin o z, weighted_spin_single o, weighted_spin_single z,
    mul_comm (weightedExpectation G β J h (spinProd ({o} : Finset V)))]
  exact weightedField_covariance_sourcePair G β h J o z


theorem weighted_deriv_magnetization_eq_currentDelta
    (β h : ℝ) (J : Sym2 V -> ℝ) (o : V) :
    HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
      ((1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) *
        ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
          h * ∑ z, weightedFieldDelta G β h J o z)) β := by
  let Z : ℝ := currentSum (withGhost G) β (ghostCoupling h β J) ∅
  let bondCov : Sym2 V -> ℝ := fun e =>
    weightedExpectation G β J h (fun s => spin s o * bond s e) -
      weightedExpectation G β J h (fun s => spin s o) *
        weightedExpectation G β J h (fun s => bond s e)
  let fieldCov : V -> ℝ := fun z =>
    weightedExpectation G β J h (fun s => spin s o * spin s z) -
      weightedExpectation G β J h (fun s => spin s o) *
        weightedExpectation G β J h (fun s => spin s z)
  have hZne : Z ≠ 0 := ne_of_gt
    (Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J))
  have hbond (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      Z ^ 2 * bondCov e = weightedBondDelta G β h J o e := by
    simpa [Z, bondCov] using weightedBond_covariance_eq_delta G β h J o e he
  have hfield (z : V) :
      Z ^ 2 * fieldCov z = weightedFieldDelta G β h J o z := by
    simpa [Z, fieldCov] using weightedField_covariance_eq_delta G β h J o z
  have hbondSum :
      Z ^ 2 * (∑ e ∈ G.edgeFinset, J e * bondCov e) =
        ∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e he => by rw [← hbond e he]; ring)
  have hfieldSum :
      Z ^ 2 * (∑ z, fieldCov z) = ∑ z, weightedFieldDelta G β h J o z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hfield z)
  have hscaled :
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z) =
        (∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
          h * ∑ z, weightedFieldDelta G β h J o z := by
    calc
      Z ^ 2 * ((∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z) =
          Z ^ 2 * (∑ e ∈ G.edgeFinset, J e * bondCov e) +
            h * (Z ^ 2 * ∑ z, fieldCov z) := by ring
      _ = _ := by rw [hbondSum, hfieldSum]
  have hvalue :
      (∑ e ∈ G.edgeFinset, J e * bondCov e) + h * ∑ z, fieldCov z =
        (1 / Z ^ 2) *
          ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
            h * ∑ z, weightedFieldDelta G β h J o z) := by
    rw [← hscaled]
    field_simp
  have hd := hasDerivAt_weightedMagnetization G β h J o
  change HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
    ((1 / Z ^ 2) *
      ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
        h * ∑ z, weightedFieldDelta G β h J o z)) β
  rw [← hvalue]
  simpa [bondCov, fieldCov] using hd

theorem ghostCoupling_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e : Sym2 (Option V), 0 ≤ ghostCoupling h β J e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      cases a <;> cases b <;> simp [ghostCoupling, hh, hJ]

theorem weightedBondDelta_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (e : Sym2 V) : 0 ≤ weightedBondDelta G β h J o e := by
  rw [weightedBondDelta, ← HcovAssembly.hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β J) (hcaBondSource o e) (by simp)]
  exact HcovAssembly.hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β J)
    hβ (ghostCoupling_nonneg β h J hh hJ) (hcaBondSource o e) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)

theorem weightedFieldDelta_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e)
    (o z : V) : 0 ≤ weightedFieldDelta G β h J o z := by
  rw [weightedFieldDelta, ← HcovAssembly.hca_pairSum_disconn_eq (withGhost G) β
    (ghostCoupling h β J) (hcaFieldSource o z) (by simp)]
  exact HcovAssembly.hca_pairSum_nonneg (withGhost G) β (ghostCoupling h β J)
    hβ (ghostCoupling_nonneg β h J hh hJ) (hcaFieldSource o z) (by simp)
    (fun m => ¬ connK (endsM (withGhost G) m) univ (some o) none) (fun _ hm => hm)

theorem weighted_currentDelta_derivative_nonneg (β h : ℝ) (J : Sym2 V -> ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJ : ∀ e, 0 ≤ J e) (o : V) :
    0 ≤ (1 / (currentSum (withGhost G) β (ghostCoupling h β J) ∅) ^ 2) *
      ((∑ e ∈ G.edgeFinset, J e * weightedBondDelta G β h J o e) +
        h * ∑ z, weightedFieldDelta G β h J o z) := by
  have hZpos := Ising.acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β J)
  refine mul_nonneg (by positivity) (add_nonneg ?_ (mul_nonneg hh ?_))
  · exact Finset.sum_nonneg (fun e _ =>
      mul_nonneg (hJ e) (weightedBondDelta_nonneg G β h J hβ hh hJ o e))
  · exact Finset.sum_nonneg (fun z _ =>
      weightedFieldDelta_nonneg G β h J hβ hh hJ o z)

end WeightedFieldGhost
end Sharpness
end StatMech
