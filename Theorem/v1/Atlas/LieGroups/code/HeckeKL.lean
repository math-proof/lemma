/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HeckeKL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part2


noncomputable section

open Polynomial

attribute [instance] CoxeterGroupData.grpInst CoxeterGroupData.finInst
  CoxeterGroupData.decEq

theorem simpleActOnLinComb_single (C : CoxeterGroupData) (s w : C.W) (c : HeckeCoeffRing) :
    simpleActOnLinComb C s (Finsupp.single w c) = c • simpleReflMulBasis C s w := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_single_index]
  simp [zero_smul]

theorem heckeMulBasis_one_left (C : CoxeterGroupData) (w : C.W) :
    heckeMulBasis C 1 w = Finsupp.single w 1 := by
  simp [heckeMulBasis]

theorem heckeMulBasis_one_right (C : CoxeterGroupData) (w₁ : C.W) :
    heckeMulBasis C w₁ 1 = Finsupp.single w₁ 1 := by
  induction hn : C.length w₁ using Nat.strongRecOn generalizing w₁ with
  | ind n ih =>
  by_cases hw₁ : w₁ = 1
  · subst hw₁; simp [heckeMulBasis]
  · rw [heckeMulBasis]; simp only [hw₁, ↓reduceDIte]
    set s := C.descentRefl w₁
    set w₁' := s * w₁
    have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
    have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
    have sw₁'_eq : s * w₁' = w₁ := C.simple_cancel s hs w₁
    have ih_w₁' : heckeMulBasis C w₁' 1 = Finsupp.single w₁' 1 :=
      ih (C.length w₁') (by omega) w₁' rfl
    rw [ih_w₁', simpleActOnLinComb_single, one_smul]
    unfold simpleReflMulBasis
    have : C.length (s * w₁') = C.length w₁' + 1 := by
      rcases C.exchange_left s hs w₁' with h | h
      · exact h
      · exfalso; rw [sw₁'_eq] at h; omega
    rw [if_pos this, sw₁'_eq]

theorem heckeMulBasis_simple (C : CoxeterGroupData) (s : C.W) (hs : s ∈ C.simpleReflections) (w : C.W) :
    heckeMulBasis C s w = simpleReflMulBasis C s w := by
  have hs_ne : s ≠ 1 := C.simple_ne_one s hs
  rw [heckeMulBasis]
  simp only [hs_ne, ↓reduceDIte]
  rw [C.descentRefl_of_simple s hs, C.simple_sq s hs]
  rw [show heckeMulBasis C 1 w = Finsupp.single w 1 from by simp [heckeMulBasis]]
  rw [simpleActOnLinComb_single, one_smul]

theorem heckeMulBasis_descent (C : CoxeterGroupData) (w₁ : C.W) (hw₁ : w₁ ≠ 1) :
    heckeMulBasis C (C.descentRefl w₁) (C.descentRefl w₁ * w₁) = Finsupp.single w₁ 1 := by
  set s := C.descentRefl w₁
  set w₁' := s * w₁
  have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
  have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
  have sw₁'_eq : s * w₁' = w₁ := C.simple_cancel s hs w₁
  rw [heckeMulBasis_simple C s hs w₁']
  unfold simpleReflMulBasis
  rcases C.exchange_left s hs w₁' with h | h
  ·
    rw [if_pos h, sw₁'_eq]
  ·
    exfalso; rw [sw₁'_eq] at h; omega

theorem heckeMulBasis_unfold (C : CoxeterGroupData) (w₁ : C.W) (hw₁ : w₁ ≠ 1) (w₂ : C.W) :
    heckeMulBasis C w₁ w₂ =
    simpleActOnLinComb C (C.descentRefl w₁) (heckeMulBasis C (C.descentRefl w₁ * w₁) w₂) := by
  rw [heckeMulBasis]
  simp [hw₁]

theorem simpleActOnLinComb_add (C : CoxeterGroupData) (s : C.W)
    (f g : HeckeAlgebra C) :
    simpleActOnLinComb C s (f + g) =
    simpleActOnLinComb C s f + simpleActOnLinComb C s g := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_add_index' (fun w => by simp [zero_smul]) (fun w a₁ a₂ => by rw [add_smul])]

theorem simpleActOnLinComb_quadratic (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (w : C.W) :
    simpleActOnLinComb C s (simpleReflMulBasis C s w) =
    hecke_q • Finsupp.single w 1 + (hecke_q - 1) • simpleReflMulBasis C s w := by

  have hss : s * s = (1 : C.W) := C.simple_sq s hs
  have cancel : s * (s * w) = w := C.simple_cancel s hs w

  rcases C.exchange_left s hs w with hup | hdown
  ·

    have hdef : simpleReflMulBasis C s w = Finsupp.single (s * w) 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup]
    rw [hdef]

    rw [simpleActOnLinComb_single, one_smul]


    have hdown_sw : ¬ (C.length (s * (s * w)) = C.length (s * w) + 1) := by
      rw [cancel]; omega
    unfold simpleReflMulBasis
    rw [if_neg hdown_sw, cancel]


    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [add_comm]
  ·

    have hdef : simpleReflMulBasis C s w = Finsupp.single w (hecke_q - 1) + Finsupp.single (s * w) hecke_q := by
      unfold simpleReflMulBasis
      rw [if_neg (by omega : ¬ (C.length (s * w) = C.length w + 1))]
    rw [hdef]

    rw [simpleActOnLinComb_add]

    rw [simpleActOnLinComb_single, simpleActOnLinComb_single]


    have hup_sw : C.length (s * (s * w)) = C.length (s * w) + 1 := by
      rw [cancel]; omega
    have hdef_sw : simpleReflMulBasis C s (s * w) = Finsupp.single w 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup_sw, cancel]
    rw [hdef, hdef_sw]

    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [smul_add]
    simp only [Finsupp.smul_single, smul_eq_mul]


    ring_nf
    rw [add_comm]

theorem simpleActOnLinComb_smul (C : CoxeterGroupData) (s : C.W)
    (c : HeckeCoeffRing) (f : HeckeAlgebra C) :
    simpleActOnLinComb C s (c • f) = c • simpleActOnLinComb C s f := by
  unfold simpleActOnLinComb
  rw [Finsupp.sum_smul_index' (fun i => by simp [zero_smul])]
  rw [Finsupp.smul_sum]
  congr 1; ext1 w; ext1 d
  exact smul_assoc c d (simpleReflMulBasis C s w)

theorem heckeMulBasis_assoc_gen_rhs (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (w₂ w₃ : C.W) :
    (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) =
    simpleActOnLinComb C s (heckeMulBasis C w₂ w₃) := by
  unfold simpleActOnLinComb
  congr 1; ext1 v; ext1 c
  rw [heckeMulBasis_simple C s hs v]

theorem simpleActOnLinComb_quadratic_gen (C : CoxeterGroupData) (s : C.W)
    (hs : s ∈ C.simpleReflections) (f : HeckeAlgebra C) :
    simpleActOnLinComb C s (simpleActOnLinComb C s f) =
    (hecke_q - 1) • simpleActOnLinComb C s f + hecke_q • f := by
  induction f using Finsupp.induction_linear with
  | zero =>
    simp only [simpleActOnLinComb, Finsupp.sum_zero_index, smul_zero, add_zero]
  | add f g hf hg =>
    rw [simpleActOnLinComb_add, simpleActOnLinComb_add, hf, hg]
    rw [smul_add, smul_add]
    abel
  | single w c =>

    conv_lhs => rw [show Finsupp.single w c = c • Finsupp.single w 1 from
      by rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    rw [simpleActOnLinComb_smul, simpleActOnLinComb_single, one_smul]

    rw [simpleActOnLinComb_smul]

    rw [simpleActOnLinComb_quadratic C s hs w]


    conv_rhs => rw [show Finsupp.single w c = c • Finsupp.single w 1 from
      by rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    rw [simpleActOnLinComb_smul, simpleActOnLinComb_single, one_smul]
    rw [smul_add, smul_comm c (hecke_q - 1), smul_comm c hecke_q]
    rw [add_comm]

theorem heckeMulBasis_assoc_gen (C : CoxeterGroupData)
    (s : C.W) (hs : s ∈ C.simpleReflections) (w₂ w₃ : C.W) :
  (heckeMulBasis C s w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
  (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C s v) := by

  rw [heckeMulBasis_assoc_gen_rhs C s hs]

  rw [heckeMulBasis_simple C s hs w₂]

  induction hn : C.length w₂ using Nat.strongRecOn generalizing w₂ with
  | ind n ih =>

  by_cases hw₂ : w₂ = 1
  · subst hw₂
    have hup : C.length (s * 1) = C.length 1 + 1 := by
      rw [mul_one, C.length_simple s hs, C.length_one]
    have heval : simpleReflMulBasis C s 1 = Finsupp.single (s * 1) 1 := by
      unfold simpleReflMulBasis; rw [if_pos hup]
    rw [heval]
    rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul]
    rw [mul_one]
    rw [heckeMulBasis_one_left]
    rw [simpleActOnLinComb_single, one_smul]
    rw [heckeMulBasis_simple C s hs w₃]
  ·
    rcases C.exchange_left s hs w₂ with hup | hdown
    ·
      have heval : simpleReflMulBasis C s w₂ = Finsupp.single (s * w₂) 1 := by
        unfold simpleReflMulBasis; rw [if_pos hup]
      rw [heval]
      rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul]
      have hsw₂_ne : s * w₂ ≠ 1 := by
        intro h; have := C.length_one ▸ h ▸ hup; omega
      rw [heckeMulBasis_unfold C (s * w₂) hsw₂_ne w₃]
      rw [C.descentRefl_of_mul s hs w₂ hup]
      rw [C.simple_cancel s hs w₂]
    ·
      have hdown' : ¬ (C.length (s * w₂) = C.length w₂ + 1) := by omega
      have heval : simpleReflMulBasis C s w₂ =
          Finsupp.single w₂ (hecke_q - 1) + Finsupp.single (s * w₂) hecke_q := by
        unfold simpleReflMulBasis; rw [if_neg hdown']
      rw [heval]
      rw [Finsupp.sum_add_index' (fun w => by simp [zero_smul]) (fun w a₁ a₂ => by rw [add_smul])]
      rw [Finsupp.sum_single_index (by simp [zero_smul])]
      rw [Finsupp.sum_single_index (by simp [zero_smul])]
      have cancel : s * (s * w₂) = w₂ := C.simple_cancel s hs w₂
      have hup_sw₂ : C.length (s * (s * w₂)) = C.length (s * w₂) + 1 := by
        rw [cancel]; omega
      have heval_sw₂ : simpleReflMulBasis C s (s * w₂) = Finsupp.single (s * (s * w₂)) 1 := by
        unfold simpleReflMulBasis; rw [if_pos hup_sw₂]
      have ih_sw₂ : (simpleReflMulBasis C s (s * w₂)).sum (fun v c => c • heckeMulBasis C v w₃) =
          simpleActOnLinComb C s (heckeMulBasis C (s * w₂) w₃) :=
        ih (C.length (s * w₂)) (by omega) (s * w₂) rfl
      rw [heval_sw₂, cancel] at ih_sw₂
      rw [Finsupp.sum_single_index (by simp [zero_smul]), one_smul] at ih_sw₂

      set X := heckeMulBasis C (s * w₂) w₃
      rw [ih_sw₂]
      rw [simpleActOnLinComb_quadratic_gen C s hs X]


theorem finsupp_sum_comm_smul {W : Type*} {R : Type*} [CommRing R]
    (g : W → W →₀ R) (outer : W →₀ R) (inner : W → W →₀ R) :
    outer.sum (fun v c => c • (inner v).sum (fun u d => d • g u)) =
    (outer.sum (fun v c => c • inner v)).sum (fun u d => d • g u) := by
  rw [Finsupp.sum_sum_index (fun a => by simp [zero_smul]) (fun a b₁ b₂ => by rw [add_smul])]
  congr 1; ext1 v; ext1 c
  rw [Finsupp.sum_smul_index' (fun i => by simp [zero_smul])]
  rw [Finsupp.smul_sum]
  congr 1; ext1 i; ext1 d'
  exact (smul_assoc c d' (g i)).symm

theorem heckeMulBasis_assoc (C : CoxeterGroupData) (w₁ w₂ w₃ : C.W) :
  (heckeMulBasis C w₁ w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
  (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁ v) := by

  induction hn : C.length w₁ using Nat.strongRecOn generalizing w₁ with
  | ind n ih =>
  by_cases hw₁ : w₁ = 1
  ·
    subst hw₁

    rw [heckeMulBasis_one_left]
    rw [Finsupp.sum_single_index (by simp [zero_smul])]
    rw [one_smul]


    symm
    have : ∀ v (c : HeckeCoeffRing), c • heckeMulBasis C 1 v = Finsupp.single v c := by
      intro v c; rw [heckeMulBasis_one_left, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp_rw [this]
    exact Finsupp.sum_single _
  ·

    set s := C.descentRefl w₁
    set w₁' := s * w₁
    have hs : s ∈ C.simpleReflections := C.descentRefl_simple w₁ hw₁
    have hlen : C.length w₁' < C.length w₁ := C.descentRefl_length w₁ hw₁
    have hdescent : heckeMulBasis C s w₁' = Finsupp.single w₁ 1 :=
      heckeMulBasis_descent C w₁ hw₁


    have hw₁_expand : ∀ w : C.W, heckeMulBasis C w₁ w =
        (heckeMulBasis C w₁' w).sum (fun v c => c • heckeMulBasis C s v) := by
      intro w
      have := heckeMulBasis_assoc_gen C s hs w₁' w
      rw [hdescent, Finsupp.sum_single_index (by simp [zero_smul]), one_smul] at this
      exact this

    have ih_w₁' :
        (heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C v w₃) =
        (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁' v) :=
      ih (C.length w₁') (by omega) w₁' rfl

    calc (heckeMulBasis C w₁ w₂).sum (fun v c => c • heckeMulBasis C v w₃)

        _ = ((heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C s v)).sum
              (fun u d => d • heckeMulBasis C u w₃) := by
            rw [hw₁_expand w₂]

        _ = (heckeMulBasis C w₁' w₂).sum (fun v c =>
              c • (heckeMulBasis C s v).sum (fun u d => d • heckeMulBasis C u w₃)) := by
            rw [← finsupp_sum_comm_smul (fun u => heckeMulBasis C u w₃)
                  (heckeMulBasis C w₁' w₂) (fun v => heckeMulBasis C s v)]

        _ = (heckeMulBasis C w₁' w₂).sum (fun v c =>
              c • (heckeMulBasis C v w₃).sum (fun u d => d • heckeMulBasis C s u)) := by
            simp_rw [heckeMulBasis_assoc_gen C s hs]

        _ = ((heckeMulBasis C w₁' w₂).sum (fun v c => c • heckeMulBasis C v w₃)).sum
              (fun u d => d • heckeMulBasis C s u) := by
            rw [finsupp_sum_comm_smul (fun u => heckeMulBasis C s u)
                  (heckeMulBasis C w₁' w₂) (fun v => heckeMulBasis C v w₃)]

        _ = ((heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁' v)).sum
              (fun u d => d • heckeMulBasis C s u) := by
            rw [ih_w₁']

        _ = (heckeMulBasis C w₂ w₃).sum (fun v c =>
              c • (heckeMulBasis C w₁' v).sum (fun u d => d • heckeMulBasis C s u)) := by
            rw [← finsupp_sum_comm_smul (fun u => heckeMulBasis C s u)
                  (heckeMulBasis C w₂ w₃) (fun v => heckeMulBasis C w₁' v)]

        _ = (heckeMulBasis C w₂ w₃).sum (fun v c => c • heckeMulBasis C w₁ v) := by
            congr 1; ext1 v; ext1 c; rw [hw₁_expand v]

end
