/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoInfluence.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.Hamming
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.BeffaraDC.RussoHamming


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma expect_indicator (p : ℝ) (A : Set (ConfigSpace E)) :
    expect p (A.indicator (fun _ => (1 : ℝ))) = prob p A := rfl


lemma expect_add (p : ℝ) (f g : ConfigSpace E → ℝ) :
    expect p (fun ω => f ω + g ω) = expect p f + expect p g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_const_mul (p : ℝ) (c : ℝ) (f : ConfigSpace E → ℝ) :
    expect p (fun ω => c * f ω) = c * expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ConfigSpace E → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : expect p f ≤ expect p g := by
  unfold expect
  refine Finset.sum_le_sum (fun ω _ => ?_)
  exact mul_le_mul_of_nonneg_right (h ω) (configWeight_nonneg hp0 hp1 ω)


lemma expect_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : ConfigSpace E → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ expect p f := by
  have := expect_mono hp0 hp1 (f := fun _ => (0 : ℝ)) (g := f) h
  simpa [expect] using this


lemma configWeight_sum_one (p : ℝ) : ∑ ω : ConfigSpace E, configWeight p ω = 1 := by
  unfold configWeight edgeWeight
  rw [← Fintype.prod_sum (fun (e : E) (b : Bool) => if b then p else 1 - p)]
  refine Finset.prod_eq_one (fun e _ => ?_)
  rw [Fintype.sum_bool]; simp

omit [DecidableEq E] in


lemma configWeight_logModular (p : ℝ) (a b : ConfigSpace E) :
    configWeight p a * configWeight p b = configWeight p (a ⊔ b) * configWeight p (a ⊓ b) := by
  have coord : ∀ (φ : Bool → ℝ) (x y : Bool), φ x * φ y = φ (x ⊔ y) * φ (x ⊓ y) := by
    intro φ x y
    rcases le_total x y with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]
  unfold configWeight edgeWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [Pi.sup_apply, Pi.inf_apply]
  exact coord (fun c => if c = true then p else 1 - p) (a e) (b e)

omit [DecidableEq E] in

lemma configWeight_fkg (p : ℝ) : FKGLatticeCondition (configWeight (E := E) p) :=
  FKGLatticeCondition.of_logModular (fun a b => configWeight_logModular p a b)


theorem fkg_cov {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ConfigSpace E → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    expect p f * expect p g ≤ expect p (fun ω => f ω * g ω) := by
  have hπ0 : (0 : ConfigSpace E → ℝ) ≤ configWeight p :=
    fun ω => configWeight_nonneg hp0 hp1 ω
  have h := fkg_inequality (E := E) hπ0 (configWeight_sum_one p) (configWeight_fkg p) hf hg
  unfold expect
  calc (∑ ω, f ω * configWeight p ω) * (∑ ω, g ω * configWeight p ω)
      = (∑ ω, configWeight p ω * f ω) * (∑ ω, configWeight p ω * g ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm (f ω) _),
            Finset.sum_congr rfl (fun ω _ => mul_comm (g ω) _)]
    _ ≤ ∑ ω, configWeight p ω * (f ω * g ω) := h
    _ = ∑ ω, (fun ω => f ω * g ω) ω * configWeight p ω :=
        Finset.sum_congr rfl (fun ω _ => by ring)


end BeffaraDC
end StatMech
