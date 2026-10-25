/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part9
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_fusionStates_chosen
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (hst : st.chosen = []) :
    ∀ n, (rosenthalFusionStates 𝒜 st n).chosen =
      rosenthalInitialSegment (rosenthalFusionPoints 𝒜 st) n := by
  intro n
  induction n with
  | zero => exact hst
  | succ n ih =>
      rw [rosenthal_fusionStates_succ]
      change (rosenthalFusionStates 𝒜 st n).chosen ++
          [rosenthalFusionPoints 𝒜 st n] = _
      rw [ih]
      simp [rosenthalInitialSegment, List.range_succ]

theorem rosenthal_fusionPoints_strictMono
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    StrictMono (rosenthalFusionPoints 𝒜 st) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let cur := rosenthalFusionStates 𝒜 st n
  let step := rosenthalFusionStep 𝒜 cur
  have hstate : rosenthalFusionStates 𝒜 st (n + 1) = rosenthalFusionNext 𝒜 cur :=
    rosenthal_fusionStates_succ 𝒜 st n
  have hmem := (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point_mem
  rw [hstate] at hmem
  obtain ⟨j, hj⟩ := hmem
  change step.point <
    (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st (n + 1))).point
  rw [hstate, ← hj]
  exact step.above j

theorem rosenthal_range_fusionState_tail_subset
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    ∀ n, Set.range (rosenthalFusionStates 𝒜 st n).tail ⊆ Set.range st.tail := by
  intro n
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
      rw [rosenthal_fusionStates_succ]
      exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).tail_subset.trans ih

theorem rosenthal_range_fusionPoints_subset
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    Set.range (rosenthalFusionPoints 𝒜 st) ⊆ Set.range st.tail := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_fusionState_tail_subset 𝒜 st n
  exact (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point_mem

theorem rosenthal_initialSegment_comp_sublist
    (φ : ℕ → ℕ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    ∀ n, (rosenthalInitialSegment (φ ∘ ψ) n).Sublist
      (rosenthalInitialSegment φ (ψ n)) := by
  intro n
  induction n with
  | zero => exact List.nil_sublist _
  | succ n ih =>
      have hleft : rosenthalInitialSegment (φ ∘ ψ) (n + 1) =
          rosenthalInitialSegment (φ ∘ ψ) n ++ [φ (ψ n)] := by
        simp [rosenthalInitialSegment, List.range_succ, Function.comp_def]
      rw [hleft]
      have h₁ := ih.append_right [φ (ψ n)]
      have hmiddle : rosenthalInitialSegment φ (ψ n) ++ [φ (ψ n)] =
          rosenthalInitialSegment φ (ψ n + 1) := by
        simp [rosenthalInitialSegment, List.range_succ]
      rw [hmiddle] at h₁
      have hbound : ψ n + 1 ≤ ψ (n + 1) := Nat.succ_le_of_lt (hψ (Nat.lt_succ_self n))
      have h₂ : (rosenthalInitialSegment φ (ψ n + 1)).Sublist
          (rosenthalInitialSegment φ (ψ (n + 1))) := by
        exact (List.range_sublist.mpr hbound).map φ
      exact h₁.trans h₂

theorem rosenthal_open_ramsey
    (𝒜 : List ℕ → Prop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ((∀ θ : ℕ → ℕ, StrictMono θ → ∀ n, ¬𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) ∨
        ∀ θ : ℕ → ℕ, StrictMono θ →
          ∃ n, 𝒜 (rosenthalInitialSegment (ψ ∘ θ) n)) := by
  obtain ⟨η, hη, hdec⟩ := rosenthal_exists_deciding_subsequence 𝒜 [] φ
  let base := φ ∘ η
  have hbase : StrictMono base := hφ.comp hη
  have hrange : Set.range base ⊆ Set.range φ := Set.range_comp_subset_range η φ
  rcases hdec with ha | hr
  · refine ⟨base, hbase, hrange, Or.inr ?_⟩
    intro θ hθ
    obtain ⟨n, hn⟩ := ha θ hθ
    exact ⟨n, by simpa [base] using hn⟩
  · let st := rosenthalFusionInitial 𝒜 base hbase hr
    let ψ := rosenthalFusionPoints 𝒜 st
    have hψ : StrictMono ψ := rosenthal_fusionPoints_strictMono 𝒜 st
    have hψrange : Set.range ψ ⊆ Set.range φ :=
      (rosenthal_range_fusionPoints_subset 𝒜 st).trans hrange
    refine ⟨ψ, hψ, hψrange, Or.inl ?_⟩
    intro θ hθ n
    have hsub := rosenthal_initialSegment_comp_sublist ψ hθ n
    have hchosen : (rosenthalFusionStates 𝒜 st (θ n)).chosen =
        rosenthalInitialSegment ψ (θ n) := by
      exact rosenthal_fusionStates_chosen 𝒜 st rfl (θ n)
    have hmem : rosenthalInitialSegment (ψ ∘ θ) n ∈
        (rosenthalFusionStates 𝒜 st (θ n)).chosen.sublists := by
      rw [hchosen, List.mem_sublists]
      exact hsub
    exact rosenthal_not_mem_of_rejects
      ((rosenthalFusionStates 𝒜 st (θ n)).rejected _ hmem)

end FunctionalAnalysis.RosenthalL1Wanted
