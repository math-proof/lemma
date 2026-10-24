import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.ProjectiveComplete
open AlgebraicGeometry


/--
[lemma_16_32](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveComplete.lean)
-/
@[path]
lemma lemma_16_32
  [Field F]
  {R : ValuationSubring F}
  {n : ℕ}
  {x : Fin (n + 1) → F}
-- given
  (hx : ∀ i, x i ≠ 0) :
-- imply
  ∃ (l : F), l ≠ 0 ∧ (∀ i, l * x i ∈ (R : Set F)) ∧ (∃ i, (l * x i)⁻¹ ∈ (R : Set F)) := by
-- proof
  induction n with
  | zero =>
    refine ⟨(x 0)⁻¹, inv_ne_zero (hx 0), ?_, ⟨0, ?_⟩⟩
    · intro i
      have hi : i = 0 := by ext; omega
      subst hi; simp [inv_mul_cancel₀ (hx 0)]
    · simp [inv_mul_cancel₀ (hx 0)]
  | succ m ih =>
    let x' : Fin (m + 1) → F := fun i => x (Fin.castSucc i)
    have hx' : ∀ i, x' i ≠ 0 := fun i => hx (Fin.castSucc i)
    obtain ⟨l, hl_ne, hl_mem, ⟨j, hj_inv⟩⟩ := ih x' hx'
    by_cases hlast : l * x (Fin.last (m + 1)) ∈ (R : Set F)
    ·
      refine ⟨l, hl_ne, ?_, ⟨Fin.castSucc j, hj_inv⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      · rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        exact hl_mem ⟨i, hi⟩
      · rw [show i = Fin.last (m + 1) from by ext; simp; omega]; exact hlast
    ·
      have hlast_inv : (l * x (Fin.last (m + 1)))⁻¹ ∈ (R : Set F) :=
        (R.mem_or_inv_mem _).resolve_left hlast
      refine ⟨(x (Fin.last (m + 1)))⁻¹, inv_ne_zero (hx _), ?_,
        ⟨Fin.last (m + 1), by simp [inv_mul_cancel₀ (hx _)]⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      ·
        rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        suffices h : (x (Fin.last (m + 1)))⁻¹ * x (Fin.castSucc ⟨i, hi⟩) =
          l * x (Fin.castSucc ⟨i, hi⟩) * (l * x (Fin.last (m + 1)))⁻¹ by
          rw [h]; exact R.toSubring.mul_mem (hl_mem ⟨i, hi⟩) hlast_inv
        field_simp
      ·
        rw [show i = Fin.last (m + 1) from by ext; simp; omega]
        rw [inv_mul_cancel₀ (hx _)]; exact R.one_mem'
namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[theorem_16_33](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveComplete.lean)
-/
@[path]
lemma theorem_16_33
  [CommRing A]
  [SetLike σ A]
  [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ}
  [GradedRing 𝒜]
  [Algebra.FiniteType (𝒜 0) A] :
-- imply
  IsProper (Proj.toSpecZero 𝒜) :=
-- proof
  inferInstance


-- created on 2026-10-23
