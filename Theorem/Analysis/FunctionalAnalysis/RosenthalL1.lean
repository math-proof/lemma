/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.FunctionalAnalysis.RosenthalL1
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_accepts_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalAccepts 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalAccepts 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

theorem rosenthal_rejects_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalRejects 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalRejects 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

theorem rosenthal_exists_indices_of_range_subset
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hsub : Set.range ψ ⊆ Set.range φ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ψ = φ ∘ θ := by
  have hex : ∀ n, ∃ m, φ m = ψ n := by
    intro n
    obtain ⟨m, hm⟩ := hsub ⟨n, rfl⟩
    exact ⟨m, hm⟩
  choose θ hθ using hex
  have hθmono : StrictMono θ := by
    intro i j hij
    apply (hφ.lt_iff_lt).mp
    rw [hθ i, hθ j]
    exact hψ hij
  exact ⟨θ, hθmono, funext fun n => (hθ n).symm⟩

theorem rosenthal_decision_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) (hsub : Set.range ψ ⊆ Set.range φ)
    (hdec : rosenthalAccepts 𝒜 s φ ∨ rosenthalRejects 𝒜 s φ) :
    rosenthalAccepts 𝒜 s ψ ∨ rosenthalRejects 𝒜 s ψ := by
  obtain ⟨θ, hθ, rfl⟩ := rosenthal_exists_indices_of_range_subset hφ hψ hsub
  rcases hdec with ha | hr
  · exact Or.inl (rosenthal_accepts_subsequence ha hθ)
  · exact Or.inr (rosenthal_rejects_subsequence hr hθ)

theorem rosenthal_exists_deciding_subsequence
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (rosenthalAccepts 𝒜 s (φ ∘ ψ) ∨ rosenthalRejects 𝒜 s (φ ∘ ψ)) := by
  classical
  by_cases h : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ rosenthalAccepts 𝒜 s (φ ∘ ψ)
  · obtain ⟨ψ, hψ, ha⟩ := h
    exact ⟨ψ, hψ, Or.inl ha⟩
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    intro ψ hψ ha
    exact h ⟨ψ, hψ, by simpa using ha⟩

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
