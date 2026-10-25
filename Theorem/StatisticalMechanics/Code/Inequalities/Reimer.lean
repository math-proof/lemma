/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.Inequalities.Reimer
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E F : Type*}


theorem reimer_wprob_general_of_core (h : ReimerWprobCore) [Fintype E] [DecidableEq E]
    (φ : E → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    (A B : Set (ConfigSpace E)) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  classical
  set n := Fintype.card E with hn
  obtain ⟨e⟩ := Fintype.truncEquivFin E
  set ψ : Fin n → Bool → ℝ := fun y => φ (e.symm y) with hψ
  have hψ0 : ∀ i b, 0 ≤ ψ i b := fun i b => hφ0 (e.symm i) b
  have hψ1 : ∀ i, ψ i false + ψ i true = 1 := fun i => hφ1 (e.symm i)
  have hcore := h n ψ hψ0 hψ1 ((cfgEquiv e) ⁻¹' A) ((cfgEquiv e) ⁻¹' B)
  rw [← preimage_disjointOccurrence e A B] at hcore
  rw [wprob_transfer e φ (disjointOccurrence A B), wprob_transfer e φ A, wprob_transfer e φ B]
  exact hcore


theorem reimer_inequality_of_core (h : ReimerWprobCore) [Fintype E] [DecidableEq E]
    {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hφ1 : ∀ x, φ x false + φ x true = 1 := by
    intro _
    have h1 : (bernoulliMeasure p hp).real {false} = ((1 - p : ℝ≥0) : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
    have h2 : (bernoulliMeasure p hp).real {true} = (p : ℝ) := by
      rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
    simp only [hφ]
    rw [h1, h2, NNReal.coe_sub hp, NNReal.coe_one]
    ring
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimer_wprob_general_of_core h φ hφ0 hφ1 A B


theorem reimer_wprob_zero (φ : Fin 0 → Bool → ℝ)
    (A B : Set (ConfigSpace (Fin 0))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  have hpw : pweight φ (default : ConfigSpace (Fin 0)) = 1 := by simp [pweight]
  have hval : ∀ S : Set (ConfigSpace (Fin 0)),
      wprob φ S = S.indicator (fun _ => (1 : ℝ)) (default : ConfigSpace (Fin 0)) := by
    intro S
    simp only [wprob]
    rw [Fintype.sum_subsingleton _ (default : ConfigSpace (Fin 0)), hpw, mul_one]
  rw [hval, hval, hval, disjointOccurrence_subsingleton]
  have hAB : (A ∩ B).indicator (fun _ => (1 : ℝ))
      = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator, ha, hb, Set.mem_inter_iff]
  rw [hAB]


theorem reimerCore_holds_on_increasing
    (n : ℕ) (φ : Fin n → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin n))) (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  bk_wprob n φ hφ0 hφ1 A B hA hB


end StatMech
