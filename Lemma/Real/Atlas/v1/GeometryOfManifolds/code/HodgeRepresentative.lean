import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeRepresentative.Part2
open HodgeRepresentative


namespace HodgeRepresentative

/--
[harmonic_exact_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean)
-/
@[path]
lemma harmonic_exact_eq_zero
  {β : hd.Ωk}
-- given
  (hd : HodgeData)
  (h : hd.Ωk1)
  (hH : hd.IsHarmonic h)
  (heq : h = hd.d_k β) :
-- imply
  h = 0 := by
-- proof
  have hcoclosed : hd.dstar_k1 h = 0 := by
    unfold HodgeData.IsHarmonic HodgeData.laplacian at hH
    have key : @inner ℝ hd.Ωk1 _ (hd.d_k (hd.dstar_k1 h) + hd.dstar_k2 (hd.d_k1 h)) h
      = (0 : ℝ) := by
      rw [hH]; exact inner_zero_left (𝕜 := ℝ) h
    rw [inner_add_left] at key
    have h1 := hd.adjoint_d_k (hd.dstar_k1 h) h
    have h2 : @inner ℝ hd.Ωk1 _ (hd.dstar_k2 (hd.d_k1 h)) h =
      @inner ℝ hd.Ωk2 _ (hd.d_k1 h) (hd.d_k1 h) := by
      have := hd.adjoint_d_k1 h (hd.d_k1 h)
      rw [real_inner_comm] at this ⊢; exact this.symm
    rw [h1, h2] at key
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (by
      linarith [real_inner_self_nonneg (x := hd.dstar_k1 h),
        real_inner_self_nonneg (x := hd.d_k1 h)])
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (show @inner ℝ hd.Ωk1 _ h h = 0 from by
    calc @inner ℝ hd.Ωk1 _ h h
      = @inner ℝ hd.Ωk1 _ (hd.d_k β) h := by rw [heq]
      _ = @inner ℝ hd.Ωk _ β (hd.dstar_k1 h) := hd.adjoint_d_k β h
      _ = 0 := by rw [hcoclosed]; exact inner_zero_right (𝕜 := ℝ) β)

end HodgeRepresentative

namespace HodgeRepresentative

/--
[harmonic_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean)
-/
@[path]
lemma harmonic_sub
-- given
  (hd : HodgeData)
  (h₁ h₂ : hd.Ωk1)
  (hH1 : hd.IsHarmonic h₁)
  (hH2 : hd.IsHarmonic h₂) :
-- imply
  hd.IsHarmonic (h₁ - h₂) := by
-- proof
  unfold HodgeData.IsHarmonic HodgeData.laplacian at *
  simp only [map_sub]
  calc hd.d_k (hd.dstar_k1 h₁) - hd.d_k (hd.dstar_k1 h₂) +
    (hd.dstar_k2 (hd.d_k1 h₁) - hd.dstar_k2 (hd.d_k1 h₂))
    = (hd.d_k (hd.dstar_k1 h₁) + hd.dstar_k2 (hd.d_k1 h₁)) -
      (hd.d_k (hd.dstar_k1 h₂) + hd.dstar_k2 (hd.d_k1 h₂)) := by abel
    _ = 0 - 0 := by rw [hH1, hH2]
    _ = 0 := sub_self 0

end HodgeRepresentative

namespace HodgeRepresentative

/--
[hodge_unique_helper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean)
-/
@[path]
lemma hodge_unique_helper
  {β₁ β₂ : hd.Ωk}
-- given
  (hd : HodgeData)
  (h₁ h₂ : hd.Ωk1)
  (hH1 : hd.IsHarmonic h₁)
  (hH2 : hd.IsHarmonic h₂)
  (heq : h₁ + hd.d_k β₁ = h₂ + hd.d_k β₂) :
-- imply
  h₁ = h₂ := by
-- proof
  have hdiff_harmonic := harmonic_sub hd h₁ h₂ hH1 hH2
  have hdiff_exact : h₁ - h₂ = hd.d_k (β₂ - β₁) := by
    have hsub : h₁ + hd.d_k β₁ - (h₂ + hd.d_k β₂) = 0 := sub_eq_zero.mpr heq
    simp only [map_sub]
    exact eq_of_sub_eq_zero (show h₁ - h₂ - (hd.d_k β₂ - hd.d_k β₁) = 0 from by
      calc h₁ - h₂ - (hd.d_k β₂ - hd.d_k β₁)
        = h₁ + hd.d_k β₁ - (h₂ + hd.d_k β₂) := by abel
        _ = 0 := hsub)
  exact sub_eq_zero.mp (harmonic_exact_eq_zero hd _ hdiff_harmonic _ hdiff_exact)

end HodgeRepresentative

namespace HodgeRepresentative

/--
[hodge_representative_exists_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean)
-/
@[path]
lemma hodge_representative_exists_unique
  {gd : hd.GreenDecomp}
  {α : hd.Ωk1}
-- given
  (hd : HodgeData)
  (hclosed : hd.d_k1 α = 0) :
-- imply
  ∃! (h : hd.Ωk1), hd.IsHarmonic h ∧ ∃ (β : hd.Ωk), α = h + hd.d_k β := by
-- proof
  have hdecomp := gd.decomp α
  have h_dstar_zero : hd.dstar_k2 (hd.d_k1 (gd.G α)) = 0 := by
    have h_Hclosed := gd.H_closed α
    have h_dsq := hd.d_squared (hd.dstar_k1 (gd.G α))
    have h_apply_d : hd.d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) = 0 := by
      have h_eq : hd.d_k1 α = hd.d_k1 (gd.H α) + hd.d_k1 (hd.d_k (hd.dstar_k1 (gd.G α)))
        + hd.d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) := by
        conv_lhs => rw [hdecomp]; simp [map_add]
      simp only [hclosed, h_Hclosed, h_dsq, zero_add] at h_eq; exact h_eq.symm
    have adj := hd.adjoint_d_k1 (hd.dstar_k2 (hd.d_k1 (gd.G α))) (hd.d_k1 (gd.G α))
    rw [h_apply_d, inner_zero_left (𝕜 := ℝ)] at adj
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp adj.symm
  have h_alpha_decomp : α = gd.H α + hd.d_k (hd.dstar_k1 (gd.G α)) := by
    have := hdecomp; rw [h_dstar_zero, add_zero] at this; exact this
  refine ⟨gd.H α, ⟨gd.H_harmonic α, hd.dstar_k1 (gd.G α), h_alpha_decomp⟩, ?_⟩
  intro h' ⟨hH', β', heq'⟩
  have h_eq : h' + hd.d_k β' = gd.H α + hd.d_k (hd.dstar_k1 (gd.G α)) := by
    rw [← heq', ← h_alpha_decomp]
  exact hodge_unique_helper hd h' (gd.H α) β' (hd.dstar_k1 (gd.G α))
    hH' (gd.H_harmonic α) h_eq

end HodgeRepresentative


-- created on 2026-10-23
