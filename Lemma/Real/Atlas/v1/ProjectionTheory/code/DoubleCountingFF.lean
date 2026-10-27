import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.DoubleCountingFF
open ProjectionTheory
open Finset BigOperators


namespace ProjectionTheory

/--
[piTheta_eq_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean)
-/
@[path]
lemma piTheta_eq_subsingleton
  [Field F]
  {x₁ x₂ : F × F}
-- given
  (hne : x₁ ≠ x₂) :
-- imply
  Set.Subsingleton {θ : F | piTheta θ x₁ = piTheta θ x₂} := by
-- proof
  intro θ₁ hθ₁ θ₂ hθ₂
  simp only [Set.mem_setOf_eq, piTheta] at hθ₁ hθ₂
  by_cases h : x₁.2 = x₂.2
  · exact absurd (Prod.ext (by linear_combination hθ₁ - θ₁ * h) h) hne
  · have h' : x₁.2 - x₂.2 ≠ 0 := sub_ne_zero.mpr h
    have eq1 : θ₁ * (x₁.2 - x₂.2) = x₂.1 - x₁.1 := by linear_combination hθ₁
    have eq2 : θ₂ * (x₁.2 - x₂.2) = x₂.1 - x₁.1 := by linear_combination hθ₂
    exact mul_right_cancel₀ h' (by rw [eq1, eq2])

end ProjectionTheory

namespace ProjectionTheory

/--
[card_filter_piTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean)
-/
@[path]
lemma card_filter_piTheta_le_one
  [Field F]
  [DecidableEq F]
  {x₁ x₂ : F × F}
  {D : Finset F}
-- given
  (hne : x₁ ≠ x₂) :
-- imply
  (D.filter (fun θ => piTheta θ x₁ = piTheta θ x₂)).card ≤ 1 := by
-- proof
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact piTheta_eq_subsingleton x₁ x₂ hne ha.2 hb.2

end ProjectionTheory

namespace ProjectionTheory

/--
[sum_sq_fibers_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean)
-/
@[path]
lemma sum_sq_fibers_eq
  [Field F]
  [DecidableEq F]
  {θ : F}
  {X : Finset (F × F)} :
-- imply
  ∑ z ∈ X.image (piTheta θ), (X.filter (fun y => piTheta θ y = z)).card ^ 2 = ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card := by
-- proof
  have h := Finset.sum_comp (fun z => (X.filter (fun y => piTheta θ y = z)).card)
    (piTheta θ) (s := X)
  rw [h]; congr 1; ext z; rw [sq, smul_eq_mul]

end ProjectionTheory

namespace ProjectionTheory

/--
[double_counting_key_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean)
-/
@[path]
lemma double_counting_key_ineq
  [Field F]
  [DecidableEq F]
  [Fintype F]
  {X : Finset (F × F)}
  {D : Finset F}
  {S : ℕ}
-- given
  (hS : S > 0)
  (hS_bound : ∀ θ ∈ D, (projectionImage θ X).card ≤ S)
  (hXS : S ≤ X.card) :
-- imply
  D.card * (X.card - S) ≤ S * X.card := by
-- proof
  have lower_per_θ : ∀ θ ∈ D, X.card ^ 2 ≤
    S * ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card := by
    intro θ hθ
    have himg : (X.image (piTheta θ)).card ≤ S := hS_bound θ hθ
    calc X.card ^ 2
      = (∑ z ∈ X.image (piTheta θ), (X.filter (fun y => piTheta θ y = z)).card) ^ 2 := by
        congr 1; exact Finset.card_eq_sum_card_image (piTheta θ) X
      _ ≤ (X.image (piTheta θ)).card *
        ∑ z ∈ X.image (piTheta θ), (X.filter (fun y => piTheta θ y = z)).card ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ S * ∑ z ∈ X.image (piTheta θ), (X.filter (fun y => piTheta θ y = z)).card ^ 2 :=
        Nat.mul_le_mul_right _ himg
      _ = S * ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card := by
        rw [sum_sq_fibers_eq]
  have lower_sum : D.card * X.card ^ 2 ≤
    S * ∑ θ ∈ D, ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card := by
    calc D.card * X.card ^ 2
      = ∑ θ ∈ D, X.card ^ 2 := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ θ ∈ D, (S * ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card) :=
        Finset.sum_le_sum lower_per_θ
      _ = S * ∑ θ ∈ D, ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card := by
        rw [Finset.mul_sum]
  have upper : ∑ θ ∈ D, ∑ x ∈ X, (X.filter (fun y => piTheta θ y = piTheta θ x)).card ≤
    X.card * D.card + X.card * (X.card - 1) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm (s := D) (t := X)]
    simp_rw [Finset.sum_comm (s := D) (t := X)]
    simp_rw [← Finset.card_filter]
    suffices h : ∀ x ∈ X, ∑ y ∈ X, (D.filter (fun θ => piTheta θ y = piTheta θ x)).card ≤
      D.card + (X.card - 1) by
      calc _ ≤ ∑ x ∈ X, (D.card + (X.card - 1)) := Finset.sum_le_sum h
        _ = X.card * (D.card + (X.card - 1)) := by simp [Finset.sum_const, smul_eq_mul]
        _ = X.card * D.card + X.card * (X.card - 1) := by ring
    intro x hx
    rw [← Finset.add_sum_erase _ _ hx]
    have h1 : (D.filter (fun θ => piTheta θ x = piTheta θ x)).card = D.card := by
      congr 1; exact Finset.filter_true_of_mem (fun _ _ => rfl)
    rw [h1]
    apply Nat.add_le_add_left
    calc ∑ y ∈ X.erase x, (D.filter (fun θ => piTheta θ y = piTheta θ x)).card
      ≤ ∑ y ∈ X.erase x, 1 :=
        Finset.sum_le_sum (fun y hy =>
          card_filter_piTheta_le_one y x (Finset.ne_of_mem_erase hy) D)
      _ = (X.erase x).card := by simp
      _ = X.card - 1 := Finset.card_erase_of_mem hx
  have combined : D.card * X.card ^ 2 ≤ S * (X.card * D.card + X.card * (X.card - 1)) :=
    le_trans lower_sum (Nat.mul_le_mul_left S upper)
  have hXpos : X.card > 0 := Nat.lt_of_lt_of_le hS hXS
  zify [hXS, show 1 ≤ X.card from hXpos] at combined ⊢
  nlinarith

end ProjectionTheory

namespace ProjectionTheory

/--
[double_counting_ff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingFF.lean)
-/
@[path]
lemma double_counting_ff
  [Field F]
  [DecidableEq F]
  [Fintype F]
  {X : Finset (F × F)}
  {D : Finset F}
  {S : ℕ}
-- given
  (hX : X.Nonempty)
  (hS : S > 0)
  (hS_bound : ∀ θ ∈ D, (projectionImage θ X).card ≤ S)
  (hSX : 2 * S ≤ X.card) :
-- imply
  D.card ≤ 2 * S := by
-- proof
  have hXS : S ≤ X.card := by omega
  have key := double_counting_key_ineq X D S hS hS_bound hXS
  by_contra h_contra
  push Not at h_contra
  have hXcard_pos : X.card > 0 := hX.card_pos
  have h2 : S * X.card < (2 * S + 1) * (X.card - S) := by
    suffices h_suff : (2 * S + 1) * (X.card - S) ≥ S * X.card + 1 by omega
    nlinarith [Nat.sub_add_cancel hXS, Nat.sub_add_cancel hSX]
  have h1 : (2 * S + 1) * (X.card - S) ≤ D.card * (X.card - S) :=
    Nat.mul_le_mul_right _ (by omega)
  linarith

end ProjectionTheory


-- created on 2026-10-23
