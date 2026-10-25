import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.BKTLemma3
open BKTProof
open Finset Complex


namespace BKTProof

/--
[l2NormSqHighFreq_mono_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma3.lean)
-/
@[path]
lemma l2NormSqHighFreq_mono_of_subset
  [DecidableEq α]
  {S T : Finset α}
  {f : α → ℂ}
-- given
  (hST : S ⊆ T)
  (hS : S.Nonempty) :
-- imply
  l2NormSqHighFreq S f ≤ l2NormSqHighFreq T f := by
-- proof
  unfold l2NormSqHighFreq
  set μS := (S.card : ℂ)⁻¹ * ∑ y ∈ S, f y
  set μT := (T.card : ℂ)⁻¹ * ∑ y ∈ T, f y
  have step1 : ∑ x ∈ S, ‖f x - μS‖ ^ 2 ≤ ∑ x ∈ S, ‖f x - μT‖ ^ 2 := by
    have decomp : ∀ x ∈ S, ‖f x - μT‖ ^ 2 = ‖f x - μS‖ ^ 2 + ‖μS - μT‖ ^ 2 +
      2 * @inner ℝ ℂ _ (f x - μS) (μS - μT) := by
      intro x _
      have eq : f x - μT = (f x - μS) + (μS - μT) := by ring
      rw [eq, norm_add_sq_real]; ring
    have cross_zero : ∑ x ∈ S, @inner ℝ ℂ _ (f x - μS) (μS - μT) = 0 := by
      rw [← sum_inner (𝕜 := ℝ)]
      have sum_zero : ∑ x ∈ S, (f x - μS) = 0 := by
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, μS]
        have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
        field_simp; ring
      rw [sum_zero, inner_zero_left]
    calc ∑ x ∈ S, ‖f x - μS‖ ^ 2
      ≤ ∑ x ∈ S, ‖f x - μS‖ ^ 2 + (↑S.card * ‖μS - μT‖ ^ 2 +
        2 * ∑ x ∈ S, @inner ℝ ℂ _ (f x - μS) (μS - μT)) := by
        rw [cross_zero, mul_zero, add_zero]
        linarith [mul_nonneg (Nat.cast_nonneg' S.card) (sq_nonneg ‖μS - μT‖)]
      _ = ∑ x ∈ S, ‖f x - μT‖ ^ 2 := by
        rw [show ∑ x ∈ S, ‖f x - μT‖ ^ 2 = ∑ x ∈ S, (‖f x - μS‖ ^ 2 + ‖μS - μT‖ ^ 2 +
          2 * @inner ℝ ℂ _ (f x - μS) (μS - μT)) from sum_congr rfl decomp]
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        ring
  have step2 : ∑ x ∈ S, ‖f x - μT‖ ^ 2 ≤ ∑ x ∈ T, ‖f x - μT‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by positivity)
  linarith

end BKTProof

namespace BKTProof

/--
[l2NormHighFreq_mono_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma3.lean)
-/
@[path]
lemma l2NormHighFreq_mono_of_subset
  [DecidableEq α]
  {S T : Finset α}
  {f : α → ℂ}
-- given
  (hST : S ⊆ T)
  (hS : S.Nonempty) :
-- imply
  l2NormHighFreq S f ≤ l2NormHighFreq T f := by
-- proof
  unfold l2NormHighFreq
  exact Real.sqrt_le_sqrt (l2NormSqHighFreq_mono_of_subset hST hS f)

end BKTProof

namespace BKTProof

/--
[bkt_lemma3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma3.lean)
-/
@[path]
lemma bkt_lemma3
  {q : ℕ}
  [NeZero q]
  {f : ZMod q → ℂ} :
-- imply
  l2NormHighFreq (univ.filter (fun x : ZMod q => IsUnit x)) f ≤ l2NormHighFreq (univ : Finset (ZMod q)) f :=
-- proof
  l2NormHighFreq_mono_of_subset (filter_subset _ _)
    ⟨1, mem_filter.mpr ⟨mem_univ _, isUnit_one⟩⟩ f

end BKTProof


-- created on 2026-10-23
