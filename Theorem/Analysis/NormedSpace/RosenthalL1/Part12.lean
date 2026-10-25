/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part11
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_closed_ramsey
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (R : K → ℕ → ℕ → Prop) (hclosed : ∀ i j, IsClosed {k | R k i j})
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ((∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired R (ψ ∘ θ)) ∨
        ∀ θ : ℕ → ℕ, StrictMono θ → ¬rosenthalPaired R (ψ ∘ θ)) := by
  obtain ⟨ψ, hψ, hψrange, hhom⟩ :=
    rosenthal_open_ramsey (rosenthalPairObstruction R) hφ
  refine ⟨ψ, hψ, hψrange, ?_⟩
  rcases hhom with hnone | hall
  · left
    intro θ hθ
    by_contra hp
    obtain ⟨N, hN⟩ :=
      rosenthal_exists_finite_pair_obstruction R hclosed (ψ ∘ θ) hp
    apply hnone θ hθ (2 * N)
    refine ⟨N, by simp [rosenthalInitialSegment], ?_⟩
    rintro ⟨k, hk⟩
    apply hN
    exact ⟨k, (rosenthal_pairsHold_initial_even R k (ψ ∘ θ) N).mp hk⟩
  · right
    intro θ hθ hp
    obtain ⟨n, hn⟩ := hall θ hθ
    obtain ⟨N, hlen, hno⟩ := hn
    have hne : n = 2 * N := by
      simpa [rosenthalInitialSegment] using hlen
    subst n
    obtain ⟨k, hk⟩ := hp
    apply hno
    refine ⟨k, (rosenthal_pairsHold_initial_even R k (ψ ∘ θ) N).mpr ?_⟩
    intro j hj
    exact hk j

theorem rosenthal_finite_closed_ramsey
    {C K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (colors : Finset C) (R : C → K → ℕ → ℕ → Prop)
    (hclosed : ∀ c i j, IsClosed {k | R c k i j})
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hcover : ∀ θ : ℕ → ℕ, StrictMono θ →
      ∃ c ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
        rosenthalPaired (R c) (φ ∘ θ ∘ η)) :
    ∃ c ∈ colors, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (R c) (ψ ∘ θ) := by
  classical
  induction colors using Finset.induction_on generalizing φ with
  | empty =>
      obtain ⟨c, hc, η, hη, hp⟩ := hcover id strictMono_id
      simp at hc
  | @insert c colors hc ih =>
      obtain ⟨ψ, hψ, hψrange, hhom⟩ := rosenthal_closed_ramsey (R c) (hclosed c) hφ
      rcases hhom with hpos | hneg
      · exact ⟨c, Finset.mem_insert_self c colors, ψ, hψ, hψrange, hpos⟩
      · obtain ⟨ρ, hρ, hψeq⟩ :=
          rosenthal_exists_indices_of_range_subset hφ hψ hψrange
        have hcoverψ : ∀ θ : ℕ → ℕ, StrictMono θ →
            ∃ d ∈ colors, ∃ η : ℕ → ℕ, StrictMono η ∧
              rosenthalPaired (R d) (ψ ∘ θ ∘ η) := by
          intro θ hθ
          obtain ⟨d, hd, η, hη, hpair⟩ := hcover (ρ ∘ θ) (hρ.comp hθ)
          rw [Finset.mem_insert] at hd
          have hpair' : rosenthalPaired (R d) (ψ ∘ θ ∘ η) := by
            simpa [hψeq, Function.comp_def] using hpair
          rcases hd with rfl | hd
          · exact (hneg (θ ∘ η) (hθ.comp hη)
              (by simpa [Function.comp_def] using hpair')).elim
          · exact ⟨d, hd, η, hη, hpair'⟩
        obtain ⟨d, hd, χ, hχ, hχrange, hall⟩ := ih hψ hcoverψ
        exact ⟨d, Finset.mem_insert_of_mem hd, χ, hχ,
          hχrange.trans hψrange, hall⟩

end FunctionalAnalysis.RosenthalL1Wanted
