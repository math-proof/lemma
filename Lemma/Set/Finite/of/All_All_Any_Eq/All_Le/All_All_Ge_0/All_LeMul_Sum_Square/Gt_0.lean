import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset in


/--
[finite_nonneg_bounded_of_pd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/LatticeFiniteness.lean)
-/
@[path]
lemma finite_nonneg_bounded_of_pd
  [Fintype B]
  {f : (B → ℝ) → (B → ℝ) → ℝ}
  {C : ℝ}
  {c : ℝ}
  {S : Set (B → ℝ)}
-- given
  (hc : 0 < c)
  (hcoerce : ∀ v : B → ℝ, c * ∑ b : B, (v b) ^ 2 ≤ f v v)
  (hS_nn : ∀ α ∈ S, ∀ b : B, 0 ≤ α b)
  (hS_bdd : ∀ α ∈ S, f α α ≤ C)
  (hS_discrete : ∀ b : B, ∀ α ∈ S, ∃ n : ℤ, α b = ↑n) :
-- imply
  S.Finite := by
-- proof
  have hL2 : ∀ α ∈ S, ∑ b : B, (α b) ^ 2 ≤ C / c := by
    intro α hα
    have h1 := hcoerce α
    have h2 := hS_bdd α hα
    have hle : c * ∑ b : B, (α b) ^ 2 ≤ C := le_trans h1 h2
    have : c * (∑ b : B, (α b) ^ 2) / c ≤ C / c :=
      div_le_div_of_nonneg_right hle hc.le
    rwa [mul_div_cancel_left₀ _ (ne_of_gt hc)] at this
  have hcoord_sq : ∀ α ∈ S, ∀ b : B, (α b) ^ 2 ≤ C / c := by
    intro α hα b
    calc (α b) ^ 2
      ≤ ∑ b' : B, (α b') ^ 2 :=
        single_le_sum (fun i _ => sq_nonneg (α i)) (mem_univ b)
      _ ≤ C / c := hL2 α hα
  have hcoord : ∀ α ∈ S, ∀ b : B, α b ≤ Real.sqrt (C / c) := by
    intro α hα b
    rw [← Real.sqrt_sq (hS_nn α hα b)]
    exact Real.sqrt_le_sqrt (hcoord_sq α hα b)
  set bound := Real.sqrt (C / c)
  set T : B → Set ℝ := fun _ =>
    {x : ℝ | (∃ n : ℤ, x = ↑n) ∧ 0 ≤ x ∧ x ≤ bound}
  have hT_finite : ∀ b : B, (T b).Finite := by
    intro b
    apply Set.Finite.subset
      ((Set.finite_Icc (0 : ℤ) ⌊bound⌋).image (Int.cast : ℤ → ℝ))
    intro x ⟨⟨n, hn⟩, hx0, hxM⟩
    exact ⟨n, ⟨by exact_mod_cast hn ▸ hx0, Int.le_floor.mpr (hn ▸ hxM)⟩, hn.symm⟩
  have hS_sub : S ⊆ Set.univ.pi T := by
    intro α hα b _
    exact ⟨hS_discrete b α hα, hS_nn α hα b, hcoord α hα b⟩
  exact (Set.Finite.pi hT_finite).subset hS_sub


-- created on 2026-10-23
