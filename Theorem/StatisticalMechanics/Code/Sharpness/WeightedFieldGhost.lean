/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/WeightedFieldGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part4
import Def.StatisticalMechanics.Code.Sharpness.WeightedFieldGhost
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


theorem weightedZ_pos (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) :
    0 < weightedZ G β J h := by
  unfold weightedZ weightedWeight
  positivity

theorem weightedZ_ne_zero (β : ℝ) (J : Sym2 V -> ℝ) (h : ℝ) :
    weightedZ G β J h ≠ 0 := (weightedZ_pos G β J h).ne'


theorem ghost_weight_eq_weighted (β h : ℝ) (J : Sym2 V -> ℝ)
    (s : ConfigSpace (Option V)) :
    boltzmannJ (withGhost G) β (ghostCoupling h β J) s =
      weightedWeight G β J (h * spin s none) (fun z => s (some z)) := by
  unfold boltzmannJ weightedWeight weightedEnergy
  rw [ghost_bondSum]
  congr 1
  have hb :
      (∑ e ∈ G.edgeFinset, J e * bond s (Sym2.map some e)) =
        ∑ e ∈ G.edgeFinset, J e * bond (fun z => s (some z)) e :=
    Finset.sum_congr rfl (fun e _ => by rw [bond_map_some])
  have hs : (∑ x : V, spin s (some x)) =
      ∑ x : V, spin (fun z => s (some z)) x := rfl
  rw [hb, hs]

theorem weightedEnergy_flip (J : Sym2 V -> ℝ) (h : ℝ) (s : ConfigSpace V) :
    weightedEnergy G J (-h) (flipV s) = weightedEnergy G J h s := by
  unfold weightedEnergy
  have hb : (∑ e ∈ G.edgeFinset, J e * bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, J e * bond s e :=
    Finset.sum_congr rfl (fun e _ => by rw [bond_flipV])
  have hs : (∑ x, spin (flipV s) x) = -∑ x, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => spin_flipV s x)
  rw [hb, hs]
  ring

theorem weightedWeight_flip (β h : ℝ) (J : Sym2 V -> ℝ) (s : ConfigSpace V) :
    weightedWeight G β J (-h) (flipV s) = weightedWeight G β J h s := by
  unfold weightedWeight
  rw [weightedEnergy_flip]

theorem weightedZ_neg (β h : ℝ) (J : Sym2 V -> ℝ) :
    weightedZ G β J (-h) = weightedZ G β J h := by
  unfold weightedZ
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  exact Finset.sum_congr rfl (fun s _ => weightedWeight_flip G β h J s)

theorem weightedNum_neg_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) =
      ∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_even A hA, weightedWeight_flip]

theorem weightedNum_neg_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J (-h) s) =
      -∑ s : ConfigSpace V, spinProd A s * weightedWeight G β J h s := by
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [spinProd_flipV_odd A hA, weightedWeight_flip]
  ring

theorem partition_ghost_eq_weightedZ (β h : ℝ) (J : Sym2 V -> ℝ) :
    partitionJ (withGhost G) β (ghostCoupling h β J) = 2 * weightedZ G β J h := by
  unfold partitionJ
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          boltzmannJ (withGhost G) β (ghostCoupling h β J)
            (fun a => Option.rec b t a)) =
        weightedZ G β J (h * spinB b) := by
    intro b
    unfold weightedZ
    exact Finset.sum_congr rfl (fun t _ => by
      rw [ghost_weight_eq_weighted, split_ghost_spin])
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  rw [weightedZ_neg]
  ring

theorem num_ghost_eq_weighted_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (A.map someEmb) s *
        boltzmannJ (withGhost G) β (ghostCoupling h β J) s) =
      2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          spinProd (A.map someEmb) (fun a => Option.rec b t a) *
            boltzmannJ (withGhost G) β (ghostCoupling h β J)
              (fun a => Option.rec b t a)) =
        ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J (h * spinB b) t := by
    intro b
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [spinProd_map_some, ghost_weight_eq_weighted, split_ghost_spin]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  rw [hfalse, htrue, mul_neg_one, mul_one]
  rw [weightedNum_neg_even G β h J A hA]
  ring

theorem num_ghost_eq_weighted_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    (∑ s : ConfigSpace (Option V), spinProd (insert none (A.map someEmb)) s *
        boltzmannJ (withGhost G) β (ghostCoupling h β J) s) =
      2 * ∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J h t := by
  rw [sum_option_config]
  have hb : ∀ b : Bool,
      (∑ t : ConfigSpace V,
          spinProd (insert none (A.map someEmb)) (fun a => Option.rec b t a) *
            boltzmannJ (withGhost G) β (ghostCoupling h β J)
              (fun a => Option.rec b t a)) =
        ∑ t : ConfigSpace V, (spinB b * spinProd A t) *
          weightedWeight G β J (h * spinB b) t := by
    intro b
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [spinProd_insert_none_map_some, ghost_weight_eq_weighted, split_ghost_spin]
  rw [Fintype.sum_bool, hb, hb]
  have hfalse : spinB false = -1 := rfl
  have htrue : spinB true = 1 := rfl
  simp only [hfalse, htrue, one_mul, neg_one_mul, mul_one, mul_neg_one]
  rw [show (∑ t : ConfigSpace V, -spinProd A t * weightedWeight G β J (-h) t) =
      -∑ t : ConfigSpace V, spinProd A t * weightedWeight G β J (-h) t by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun t _ => by ring)]
  rw [weightedNum_neg_odd G β h J A hA]
  ring

theorem weightedExpectation_eq_currentRatio_even (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Even A.card) :
    weightedExpectation G β J h (spinProd A) =
      currentSum (withGhost G) β (ghostCoupling h β J) (A.map someEmb) /
        currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
  rw [← current_representation]
  unfold expectationJ weightedExpectation
  rw [partition_ghost_eq_weightedZ, num_ghost_eq_weighted_even G β h J A hA]
  field_simp [weightedZ_ne_zero G β J h]

theorem weightedExpectation_eq_currentRatio_odd (β h : ℝ) (J : Sym2 V -> ℝ)
    (A : Finset V) (hA : Odd A.card) :
    weightedExpectation G β J h (spinProd A) =
      currentSum (withGhost G) β (ghostCoupling h β J)
          (insert none (A.map someEmb)) /
        currentSum (withGhost G) β (ghostCoupling h β J) ∅ := by
  rw [← current_representation]
  unfold expectationJ weightedExpectation
  rw [partition_ghost_eq_weightedZ, num_ghost_eq_weighted_odd G β h J A hA]
  field_simp [weightedZ_ne_zero G β J h]


theorem hasDerivAt_weightedWeight (β h : ℝ) (J : Sym2 V -> ℝ)
    (s : ConfigSpace V) :
    HasDerivAt (fun β => weightedWeight G β J h s)
      (weightedWeight G β J h s * weightedEnergy G J h s) β := by
  unfold weightedWeight
  simpa [mul_comm] using
    (Real.hasDerivAt_exp (β * weightedEnergy G J h s)).comp β
      ((hasDerivAt_id β).mul_const (weightedEnergy G J h s))

theorem hasDerivAt_weightedNum (β h : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * weightedWeight G β J h s)
      (∑ s : ConfigSpace V,
        f s * (weightedWeight G β J h s * weightedEnergy G J h s)) β := by
  have hrw : (fun β => ∑ s : ConfigSpace V, f s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V, (fun β => f s * weightedWeight G β J h s) := by
    rw [Finset.sum_fn]
  rw [hrw]
  exact HasDerivAt.sum
    (fun s _ => (hasDerivAt_weightedWeight G β h J s).const_mul (f s))

theorem hasDerivAt_weightedZ (β h : ℝ) (J : Sym2 V -> ℝ) :
    HasDerivAt (fun β => weightedZ G β J h)
      (∑ s : ConfigSpace V, weightedWeight G β J h s * weightedEnergy G J h s) β := by
  simpa [weightedZ] using hasDerivAt_weightedNum G β h J (fun _ => 1)

theorem hasDerivAt_weightedExpectation (β h : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    HasDerivAt (fun β => weightedExpectation G β J h f)
      (weightedExpectation G β J h (fun s => f s * weightedEnergy G J h s) -
        weightedExpectation G β J h f *
          weightedExpectation G β J h (weightedEnergy G J h)) β := by
  have hN := hasDerivAt_weightedNum G β h J f
  have hZ := hasDerivAt_weightedZ G β h J
  have hZne := weightedZ_ne_zero G β J h
  have hdiv := hN.div hZ hZne
  have e1 : weightedExpectation G β J h (fun s => f s * weightedEnergy G J h s) =
      (∑ s : ConfigSpace V, (f s * weightedEnergy G J h s) * weightedWeight G β J h s) /
        weightedZ G β J h := rfl
  have e2 : weightedExpectation G β J h f =
      (∑ s : ConfigSpace V, f s * weightedWeight G β J h s) / weightedZ G β J h := rfl
  have e3 : weightedExpectation G β J h (weightedEnergy G J h) =
      (∑ s : ConfigSpace V, weightedEnergy G J h s * weightedWeight G β J h s) /
        weightedZ G β J h := rfl
  rw [e1, e2, e3]
  convert hdiv using 1
  field_simp [hZne]
  rw [show (∑ s : ConfigSpace V,
      f s * weightedEnergy G J h s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V,
        f s * weightedWeight G β J h s * weightedEnergy G J h s by
      exact Finset.sum_congr rfl (fun s _ => by ring),
    show (∑ s : ConfigSpace V,
      weightedEnergy G J h s * weightedWeight G β J h s) =
      ∑ s : ConfigSpace V,
        weightedWeight G β J h s * weightedEnergy G J h s by
      exact Finset.sum_congr rfl (fun s _ => by ring)]
  ring

theorem weightedExpectation_sum {ι : Type*} (β h : ℝ) (J : Sym2 V -> ℝ)
    (S : Finset ι) (f : ι -> ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => ∑ i ∈ S, f i s) =
      ∑ i ∈ S, weightedExpectation G β J h (f i) := by
  unfold weightedExpectation
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ s : ConfigSpace V, (∑ i ∈ S, f i s) * weightedWeight G β J h s) =
        ∑ s : ConfigSpace V, ∑ i ∈ S, f i s * weightedWeight G β J h s := by
          exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_mul])
    _ = ∑ i ∈ S, ∑ s : ConfigSpace V, f i s * weightedWeight G β J h s :=
      Finset.sum_comm

theorem weightedExpectation_add (β h : ℝ) (J : Sym2 V -> ℝ)
    (f g : ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => f s + g s) =
      weightedExpectation G β J h f + weightedExpectation G β J h g := by
  unfold weightedExpectation
  rw [← add_div, ← Finset.sum_add_distrib]
  exact congrArg (fun x => x / weightedZ G β J h)
    (Finset.sum_congr rfl (fun s _ => by ring))

theorem weightedExpectation_const_mul (β h c : ℝ) (J : Sym2 V -> ℝ)
    (f : ConfigSpace V -> ℝ) :
    weightedExpectation G β J h (fun s => c * f s) =
      c * weightedExpectation G β J h f := by
  unfold weightedExpectation
  rw [show (∑ s : ConfigSpace V, (fun s => c * f s) s * weightedWeight G β J h s) =
      c * ∑ s : ConfigSpace V, f s * weightedWeight G β J h s by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => by ring)]
  ring


theorem hasDerivAt_weightedMagnetization (β h : ℝ) (J : Sym2 V -> ℝ) (o : V) :
    HasDerivAt (fun β => weightedExpectation G β J h (fun s => spin s o))
      ((∑ e ∈ G.edgeFinset, J e *
          (weightedExpectation G β J h (fun s => spin s o * bond s e) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => bond s e))) +
        h * ∑ z,
          (weightedExpectation G β J h (fun s => spin s o * spin s z) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => spin s z))) β := by
  have hd := hasDerivAt_weightedExpectation G β h J (fun s => spin s o)
  have hmul : weightedExpectation G β J h
      (fun s => spin s o * weightedEnergy G J h s) =
      (∑ e ∈ G.edgeFinset, J e *
        weightedExpectation G β J h (fun s => spin s o * bond s e)) +
        h * ∑ z, weightedExpectation G β J h (fun s => spin s o * spin s z) := by
    rw [show (fun s => spin s o * weightedEnergy G J h s) =
        (fun s => (∑ e ∈ G.edgeFinset, J e * (spin s o * bond s e)) +
          h * ∑ z, spin s o * spin s z) by
      funext s
      unfold weightedEnergy
      rw [mul_add]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring)
      · rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)]
    rw [weightedExpectation_add]
    rw [weightedExpectation_sum G β h J G.edgeFinset
      (fun e s => J e * (spin s o * bond s e))]
    rw [Finset.sum_congr rfl (fun e _ => weightedExpectation_const_mul G β h (J e) J _)]
    rw [weightedExpectation_const_mul]
    congr 1
    rw [weightedExpectation_sum G β h J Finset.univ
      (fun z s => spin s o * spin s z)]
  have henergy : weightedExpectation G β J h (weightedEnergy G J h) =
      (∑ e ∈ G.edgeFinset, J e * weightedExpectation G β J h (fun s => bond s e)) +
        h * ∑ z, weightedExpectation G β J h (fun s => spin s z) := by
    unfold weightedEnergy
    rw [weightedExpectation_add]
    rw [weightedExpectation_sum G β h J G.edgeFinset (fun e s => J e * bond s e)]
    rw [Finset.sum_congr rfl (fun e _ => weightedExpectation_const_mul G β h (J e) J _)]
    rw [weightedExpectation_const_mul]
    congr 1
    rw [weightedExpectation_sum G β h J Finset.univ (fun z s => spin s z)]
  let m := weightedExpectation G β J h (fun s => spin s o)
  have hb :
      (∑ e ∈ G.edgeFinset, J e *
        (weightedExpectation G β J h (fun s => spin s o * bond s e) -
          m * weightedExpectation G β J h (fun s => bond s e))) =
      (∑ e ∈ G.edgeFinset,
        J e * weightedExpectation G β J h (fun s => spin s o * bond s e)) -
        m * ∑ e ∈ G.edgeFinset,
          J e * weightedExpectation G β J h (fun s => bond s e) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => by ring)
  have hf :
      h * ∑ z, (weightedExpectation G β J h (fun s => spin s o * spin s z) -
        m * weightedExpectation G β J h (fun s => spin s z)) =
      h * ∑ z, weightedExpectation G β J h (fun s => spin s o * spin s z) -
        m * (h * ∑ z, weightedExpectation G β J h (fun s => spin s z)) := by
    rw [Finset.sum_sub_distrib, mul_sub]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro z _ <;> ring
  have hvalue :
      (∑ e ∈ G.edgeFinset, J e *
          (weightedExpectation G β J h (fun s => spin s o * bond s e) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => bond s e))) +
        h * ∑ z,
          (weightedExpectation G β J h (fun s => spin s o * spin s z) -
            weightedExpectation G β J h (fun s => spin s o) *
              weightedExpectation G β J h (fun s => spin s z)) =
      weightedExpectation G β J h (fun s => spin s o * weightedEnergy G J h s) -
        m * weightedExpectation G β J h (weightedEnergy G J h) := by
    change _ = _ - m * _
    rw [hb, hf, hmul, henergy]
    ring
  rw [hvalue]
  exact hd


end WeightedFieldGhost
end Sharpness
end StatMech
