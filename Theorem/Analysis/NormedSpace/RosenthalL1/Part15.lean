/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part14
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_exists_uniform_cell_pair
    {K 𝕜 : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [RCLike 𝕜] (f : ℕ → K → 𝕜) (hf : ∀ n, Continuous (f n))
    (B epsilon delta : ℝ) (hdelta : 0 < delta)
    (hbound : ∀ n k, ‖f n k‖ ≤ B) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsep : ∀ θ : ℕ → ℕ, StrictMono θ →
      rosenthalPaired (rosenthalGap f epsilon) (φ ∘ θ)) :
    ∃ u v : 𝕜, epsilon ≤ dist u v + 2 * delta ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
        ∀ θ : ℕ → ℕ, StrictMono θ →
          rosenthalPaired (rosenthalCellPair f delta u v) (ψ ∘ θ) := by
  classical
  obtain ⟨t, ht⟩ := rosenthal_exists_finite_scalar_net (𝕜 := 𝕜) B delta hdelta
  let colors := (t.product t).filter fun uv => epsilon ≤ dist uv.1 uv.2 + 2 * delta
  let R : 𝕜 × 𝕜 → K → ℕ → ℕ → Prop := fun uv =>
    rosenthalCellPair f delta uv.1 uv.2
  have hclosed : ∀ c i j, IsClosed {k | R c k i j} := by
    intro c i j
    exact (isClosed_le ((hf i).dist continuous_const) continuous_const).and
      (isClosed_le ((hf j).dist continuous_const) continuous_const)
  have hcover : ∀ θ : ℕ → ℕ, StrictMono θ →
      ∃ c ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
        rosenthalPaired (R c) (φ ∘ θ ∘ η) := by
    intro θ hθ
    obtain ⟨k, hgap⟩ := hsep θ hθ
    have hpick : ∀ n, ∃ c : ↑(t.product t),
        dist (f ((φ ∘ θ) (2 * n)) k) c.1.1 ≤ delta ∧
          dist (f ((φ ∘ θ) (2 * n + 1)) k) c.1.2 ≤ delta := by
      intro n
      obtain ⟨u, hu, hfu⟩ := ht _ (hbound _ _)
      obtain ⟨v, hv, hfv⟩ := ht _ (hbound _ _)
      exact ⟨⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩⟩, hfu, hfv⟩
    choose color hleft hright using hpick
    obtain ⟨c, hcinf⟩ := Finite.exists_infinite_fiber color
    have hinf : (color ⁻¹' ({c} : Set _)).Infinite := Set.infinite_coe_iff.mp hcinf
    let η : ℕ → ℕ := Nat.nth fun n => n ∈ color ⁻¹' ({c} : Set _)
    have hη : StrictMono η := Nat.nth_strictMono hinf
    have hcolor : ∀ n, color (η n) = c := by
      intro n
      simpa [η] using Nat.nth_mem_of_infinite hinf n
    have hvalid : epsilon ≤ dist c.1.1 c.1.2 + 2 * delta := by
      have hc0 := hcolor 0
      have hl := hleft (η 0)
      have hr := hright (η 0)
      rw [hc0] at hl hr
      have htri := dist_triangle4
        (f ((φ ∘ θ) (2 * η 0)) k) c.1.1 c.1.2
        (f ((φ ∘ θ) (2 * η 0 + 1)) k)
      have hg := hgap (η 0)
      rw [rosenthalGap] at hg
      have hr' : dist c.1.2 (f ((φ ∘ θ) (2 * η 0 + 1)) k) ≤ delta := by
        simpa [dist_comm] using hr
      linarith
    refine ⟨c.1, ?_, rosenthalPairLift η, rosenthal_pairLift_strictMono hη, ?_⟩
    · exact Finset.mem_filter.mpr ⟨c.2, hvalid⟩
    · refine ⟨k, ?_⟩
      intro n
      have hc := hcolor n
      have hl := hleft (η n)
      have hr := hright (η n)
      rw [hc] at hl hr
      simpa [R, rosenthalCellPair, Function.comp_def,
        rosenthal_pairLift_even, rosenthal_pairLift_odd] using And.intro hl hr
  obtain ⟨c, hc, ψ, hψ, hψrange, hall⟩ :=
    rosenthal_finite_closed_ramsey colors R hclosed hφ hcover
  exact ⟨c.1, c.2, (Finset.mem_filter.mp hc).2, ψ, hψ, hψrange, hall⟩

end FunctionalAnalysis.RosenthalL1Wanted
