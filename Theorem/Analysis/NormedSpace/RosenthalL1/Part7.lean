/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part7
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_manyPoints_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyPoints 𝒜 ss φ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [rosenthalManyPoints, rosenthalManyPoints, rosenthal_manyChain_succ]
  exact rosenthal_manyNext_above 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) 0

theorem rosenthal_range_manyPoints_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyPoints 𝒜 ss φ) ⊆ Set.range φ := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_manyChain_mono 𝒜 ss φ (Nat.zero_le n)
  exact ⟨0, rfl⟩

theorem rosenthal_manyPoints_tail_subsequence
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧
      rosenthalTail (rosenthalManyPoints 𝒜 ss φ ∘ ψ) =
        rosenthalManyChain 𝒜 ss φ (ψ 0 + 1) ∘ θ := by
  let p := rosenthalManyPoints 𝒜 ss φ
  let q := rosenthalTail (p ∘ ψ)
  have hp : StrictMono p := rosenthal_manyPoints_strictMono 𝒜 ss hφ
  have hq : StrictMono q := rosenthal_tail_strictMono (hp.comp hψ)
  have hsub : Set.range q ⊆
      Set.range (rosenthalManyChain 𝒜 ss φ (ψ 0 + 1)) := by
    rintro _ ⟨j, rfl⟩
    have hle : ψ 0 + 1 ≤ ψ (j + 1) := Nat.succ_le_of_lt (hψ (Nat.zero_lt_succ j))
    apply rosenthal_range_manyChain_mono 𝒜 ss φ hle
    exact ⟨0, rfl⟩
  exact rosenthal_exists_indices_of_range_subset
    (rosenthal_manyChain_strictMono 𝒜 ss hφ (ψ 0 + 1)) hq hsub

theorem rosenthal_manyPoints_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : List ℕ} (hs : s ∈ ss) (n : ℕ) :
    rosenthalAccepts 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) ∨
      rosenthalRejects 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
  rw [rosenthal_manyChain_succ]
  exact rosenthal_manyNext_decides 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) s hs

theorem rosenthal_manyPoints_eventually_rejects
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : List ℕ} (hs : s ∈ ss) (hrej : rosenthalRejects 𝒜 s φ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      rosenthalRejects 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
  classical
  by_contra hb
  push Not at hb
  have hunbounded : ∀ N : ℕ, ∃ n > N,
      rosenthalAccepts 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
    intro N
    obtain ⟨n, hn, hnrej⟩ := hb (N + 1)
    refine ⟨n, lt_of_lt_of_le (Nat.lt_succ_self N) hn, ?_⟩
    rcases rosenthal_manyPoints_decides 𝒜 ss hφ hs n with ha | hr
    · exact ha
    · exact False.elim (hnrej hr)
  obtain ⟨η, hη, hηacc⟩ := Nat.exists_strictMono_subsequence hunbounded
  let p := rosenthalManyPoints 𝒜 ss φ
  have hp : StrictMono p := rosenthal_manyPoints_strictMono 𝒜 ss hφ
  let q := p ∘ η
  have hq : StrictMono q := hp.comp hη
  have hqacc : rosenthalAccepts 𝒜 s q := by
    intro ψ hψ
    obtain ⟨θ, hθ, htail⟩ := rosenthal_manyPoints_tail_subsequence 𝒜 ss hφ (hη.comp hψ)
    obtain ⟨k, hk⟩ := hηacc (ψ 0) θ hθ
    refine ⟨k + 1, ?_⟩
    rw [rosenthal_initialSegment_succ]
    have htail' : rosenthalInitialSegment
        (rosenthalManyChain 𝒜 ss φ (η (ψ 0) + 1) ∘ θ) k =
        rosenthalInitialSegment (rosenthalTail (q ∘ ψ)) k := by
      simpa [p, q, Function.comp_def] using
        congrArg (fun q => rosenthalInitialSegment q k) htail.symm
    rw [← htail']
    simpa [p, q, Function.comp_def, List.append_assoc] using hk
  have hqrange : Set.range q ⊆ Set.range φ :=
    (Set.range_comp_subset_range η p).trans
      (rosenthal_range_manyPoints_subset 𝒜 ss φ)
  obtain ⟨θ, hθ, hqcomp⟩ := rosenthal_exists_indices_of_range_subset hφ hq hqrange
  exact hrej θ hθ (by simpa [hqcomp] using hqacc)

theorem rosenthal_rejected_extensions_step
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hrej : ∀ s ∈ ss, rosenthalRejects 𝒜 s φ) :
    ∃ m : ℕ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ j, m < ψ j) ∧
      Set.range ψ ⊆ Set.range φ ∧ m ∈ Set.range φ ∧
      ∀ s ∈ ss, rosenthalRejects 𝒜 (s ++ [m]) ψ := by
  have hcommon : ∀ tt : List (List ℕ), (∀ t ∈ tt, t ∈ ss) →
      ∃ N : ℕ, ∀ t ∈ tt, ∀ n, N ≤ n →
        rosenthalRejects 𝒜 (t ++ [rosenthalManyPoints 𝒜 ss φ n])
          (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
    intro tt htt
    induction tt with
    | nil => exact ⟨0, by simp⟩
    | cons t ts ih =>
        obtain ⟨Nt, hNt⟩ := rosenthal_manyPoints_eventually_rejects
          𝒜 ss hφ (htt t (List.mem_cons_self)) (hrej t (htt t (List.mem_cons_self)))
        obtain ⟨Ns, hNs⟩ := ih (fun u hu => htt u (List.mem_cons_of_mem _ hu))
        refine ⟨max Nt Ns, ?_⟩
        intro u hu n hn
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hNt n ((le_max_left _ _).trans hn)
        · exact hNs u hu n ((le_max_right _ _).trans hn)
  obtain ⟨N, hN⟩ := hcommon ss (fun _ h => h)
  let m := rosenthalManyPoints 𝒜 ss φ N
  let ψ := rosenthalManyChain 𝒜 ss φ (N + 1)
  have hψ : StrictMono ψ := rosenthal_manyChain_strictMono 𝒜 ss hφ (N + 1)
  refine ⟨m, ψ, hψ, ?_, ?_, ?_, ?_⟩
  · intro j
    change rosenthalManyChain 𝒜 ss φ N 0 <
      rosenthalManyChain 𝒜 ss φ (N + 1) j
    rw [rosenthal_manyChain_succ]
    exact rosenthal_manyNext_above 𝒜 ss
      (rosenthal_manyChain_strictMono 𝒜 ss hφ N) j
  · exact rosenthal_range_manyChain_mono 𝒜 ss φ (Nat.zero_le (N + 1))
  · exact rosenthal_range_manyPoints_subset 𝒜 ss φ ⟨N, rfl⟩
  · intro s hs
    exact hN s hs N le_rfl

end FunctionalAnalysis.RosenthalL1Wanted
