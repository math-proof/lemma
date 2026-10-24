/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth

/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

private def rosenthalInitialSegment (φ : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map φ

private def rosenthalAccepts (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ →
    ∃ n : ℕ, 𝒜 (s ++ rosenthalInitialSegment (φ ∘ ψ) n)

private def rosenthalRejects (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ → ¬ rosenthalAccepts 𝒜 s (φ ∘ ψ)

private theorem rosenthal_accepts_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalAccepts 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalAccepts 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

private theorem rosenthal_rejects_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ : ℕ → ℕ}
    (h : rosenthalRejects 𝒜 s φ) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    rosenthalRejects 𝒜 s (φ ∘ ψ) := by
  intro θ hθ
  simpa [Function.comp_def] using h (ψ ∘ θ) (hψ.comp hθ)

private theorem rosenthal_exists_indices_of_range_subset
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

private theorem rosenthal_decision_subsequence
    {𝒜 : List ℕ → Prop} {s : List ℕ} {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) (hsub : Set.range ψ ⊆ Set.range φ)
    (hdec : rosenthalAccepts 𝒜 s φ ∨ rosenthalRejects 𝒜 s φ) :
    rosenthalAccepts 𝒜 s ψ ∨ rosenthalRejects 𝒜 s ψ := by
  obtain ⟨θ, hθ, rfl⟩ := rosenthal_exists_indices_of_range_subset hφ hψ hsub
  rcases hdec with ha | hr
  · exact Or.inl (rosenthal_accepts_subsequence ha hθ)
  · exact Or.inr (rosenthal_rejects_subsequence hr hθ)

private theorem rosenthal_exists_deciding_subsequence
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

private def rosenthalTail (φ : ℕ → ℕ) : ℕ → ℕ :=
  fun n => φ (n + 1)

private theorem rosenthal_initialSegment_succ (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalInitialSegment φ (n + 1) =
      φ 0 :: rosenthalInitialSegment (rosenthalTail φ) n := by
  simp [rosenthalInitialSegment, List.range_succ_eq_map, rosenthalTail,
    Function.comp_def]

private theorem rosenthal_tail_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalTail φ) := by
  exact hφ.comp fun _ _ h => Nat.add_lt_add_right h 1

private noncomputable def rosenthalDecisionIndices
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) : ℕ → ℕ :=
  Classical.choose (rosenthal_exists_deciding_subsequence 𝒜 s φ)

private theorem rosenthal_decisionIndices_strictMono
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    StrictMono (rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).1

private theorem rosenthal_decisionIndices_decides
    (𝒜 : List ℕ → Prop) (s : List ℕ) (φ : ℕ → ℕ) :
    rosenthalAccepts 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) ∨
      rosenthalRejects 𝒜 s (φ ∘ rosenthalDecisionIndices 𝒜 s φ) :=
  (Classical.choose_spec (rosenthal_exists_deciding_subsequence 𝒜 s φ)).2

private noncomputable def rosenthalDecideMany
    (𝒜 : List ℕ → Prop) : List (List ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | [], φ => φ
  | s :: ss, φ => rosenthalDecideMany 𝒜 ss (φ ∘ rosenthalDecisionIndices 𝒜 s φ)

private theorem rosenthal_decideMany_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => exact hφ
  | cons s ss ih =>
      exact ih (hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 s φ))

private theorem rosenthal_range_decideMany_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalDecideMany 𝒜 ss φ) ⊆ Set.range φ := by
  induction ss generalizing φ with
  | nil => exact Set.Subset.rfl
  | cons s ss ih =>
      exact (ih (φ ∘ rosenthalDecisionIndices 𝒜 s φ)).trans
        (Set.range_comp_subset_range _ _)

private theorem rosenthal_decideMany_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 s (rosenthalDecideMany 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 s (rosenthalDecideMany 𝒜 ss φ) := by
  induction ss generalizing φ with
  | nil => simp
  | cons t ts ih =>
      intro s hs
      let φ' := φ ∘ rosenthalDecisionIndices 𝒜 t φ
      have hφ' : StrictMono φ' :=
        hφ.comp (rosenthal_decisionIndices_strictMono 𝒜 t φ)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact rosenthal_decision_subsequence hφ'
          (rosenthal_decideMany_strictMono 𝒜 ts hφ')
          (rosenthal_range_decideMany_subset 𝒜 ts φ')
          (rosenthal_decisionIndices_decides 𝒜 s φ)
      · exact ih hφ' s hs

private noncomputable def rosenthalManyNext
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) : ℕ → ℕ :=
  rosenthalDecideMany 𝒜 (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ)

private theorem rosenthal_manyNext_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyNext 𝒜 ss φ) :=
  rosenthal_decideMany_strictMono 𝒜 _ (rosenthal_tail_strictMono hφ)

private theorem rosenthal_range_manyNext_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyNext 𝒜 ss φ) ⊆ Set.range φ := by
  exact (rosenthal_range_decideMany_subset 𝒜 _ _).trans
    (Set.range_comp_subset_range (fun n => n + 1) φ)

private theorem rosenthal_manyNext_above
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, φ 0 < rosenthalManyNext 𝒜 ss φ n := by
  intro n
  obtain ⟨k, hk⟩ := rosenthal_range_decideMany_subset 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) ⟨n, rfl⟩
  change φ 0 < rosenthalDecideMany 𝒜
    (ss.map fun s => s ++ [φ 0]) (rosenthalTail φ) n
  rw [← hk]
  exact hφ (Nat.zero_lt_succ k)

private theorem rosenthal_manyNext_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ s ∈ ss, rosenthalAccepts 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) ∨
      rosenthalRejects 𝒜 (s ++ [φ 0]) (rosenthalManyNext 𝒜 ss φ) := by
  intro s hs
  exact rosenthal_decideMany_decides 𝒜 _ (rosenthal_tail_strictMono hφ)
    (s ++ [φ 0]) (List.mem_map.mpr ⟨s, hs, rfl⟩)

private noncomputable def rosenthalManyChain
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  (rosenthalManyNext 𝒜 ss)^[n] φ

private theorem rosenthal_manyChain_succ
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) :
    rosenthalManyChain 𝒜 ss φ (n + 1) =
      rosenthalManyNext 𝒜 ss (rosenthalManyChain 𝒜 ss φ n) := by
  rw [show n + 1 = n.succ from rfl]
  exact Function.iterate_succ_apply' (rosenthalManyNext 𝒜 ss) n φ

private theorem rosenthal_manyChain_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ n, StrictMono (rosenthalManyChain 𝒜 ss φ n) := by
  intro n
  induction n with
  | zero => exact hφ
  | succ n ih =>
      rw [rosenthal_manyChain_succ]
      exact rosenthal_manyNext_strictMono 𝒜 ss ih

private theorem rosenthal_range_manyChain_mono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    Set.range (rosenthalManyChain 𝒜 ss φ n) ⊆
      Set.range (rosenthalManyChain 𝒜 ss φ m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hmn ih =>
      rw [rosenthal_manyChain_succ]
      exact (rosenthal_range_manyNext_subset 𝒜 ss _).trans ih

private noncomputable def rosenthalManyPoints
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) (n : ℕ) : ℕ :=
  rosenthalManyChain 𝒜 ss φ n 0

private theorem rosenthal_manyPoints_strictMono
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    StrictMono (rosenthalManyPoints 𝒜 ss φ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [rosenthalManyPoints, rosenthalManyPoints, rosenthal_manyChain_succ]
  exact rosenthal_manyNext_above 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) 0

private theorem rosenthal_range_manyPoints_subset
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) (φ : ℕ → ℕ) :
    Set.range (rosenthalManyPoints 𝒜 ss φ) ⊆ Set.range φ := by
  rintro _ ⟨n, rfl⟩
  apply rosenthal_range_manyChain_mono 𝒜 ss φ (Nat.zero_le n)
  exact ⟨0, rfl⟩

private theorem rosenthal_manyPoints_tail_subsequence
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

private theorem rosenthal_manyPoints_decides
    (𝒜 : List ℕ → Prop) (ss : List (List ℕ)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {s : List ℕ} (hs : s ∈ ss) (n : ℕ) :
    rosenthalAccepts 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) ∨
      rosenthalRejects 𝒜 (s ++ [rosenthalManyPoints 𝒜 ss φ n])
        (rosenthalManyChain 𝒜 ss φ (n + 1)) := by
  rw [rosenthal_manyChain_succ]
  exact rosenthal_manyNext_decides 𝒜 ss
    (rosenthal_manyChain_strictMono 𝒜 ss hφ n) s hs

private theorem rosenthal_manyPoints_eventually_rejects
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

private theorem rosenthal_rejected_extensions_step
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

private structure RosenthalFusionState (𝒜 : List ℕ → Prop) where
  chosen : List ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  rejected : ∀ s ∈ chosen.sublists, rosenthalRejects 𝒜 s tail

private structure RosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) where
  point : ℕ
  tail : ℕ → ℕ
  tail_strict : StrictMono tail
  above : ∀ n, point < tail n
  tail_subset : Set.range tail ⊆ Set.range st.tail
  point_mem : point ∈ Set.range st.tail
  rejected : ∀ s ∈ (st.chosen ++ [point]).sublists, rosenthalRejects 𝒜 s tail

private theorem rosenthal_fusionStep_exists
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) :
    Nonempty (RosenthalFusionStep 𝒜 st) := by
  obtain ⟨m, ψ, hψ, habove, hsub, hmem, hnew⟩ :=
    rosenthal_rejected_extensions_step 𝒜 st.chosen.sublists st.tail_strict st.rejected
  have hold : ∀ s ∈ st.chosen.sublists, rosenthalRejects 𝒜 s ψ := by
    obtain ⟨θ, hθ, hcomp⟩ :=
      rosenthal_exists_indices_of_range_subset st.tail_strict hψ hsub
    intro s hs
    rw [hcomp]
    exact rosenthal_rejects_subsequence (st.rejected s hs) hθ
  refine ⟨⟨m, ψ, hψ, habove, hsub, hmem, ?_⟩⟩
  intro s hs
  rw [List.sublists_concat] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hold s hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hnew t ht

private noncomputable def rosenthalFusionStep
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionStep 𝒜 st :=
  Classical.choice (rosenthal_fusionStep_exists 𝒜 st)

private noncomputable def rosenthalFusionNext
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) : RosenthalFusionState 𝒜 where
  chosen := st.chosen ++ [(rosenthalFusionStep 𝒜 st).point]
  tail := (rosenthalFusionStep 𝒜 st).tail
  tail_strict := (rosenthalFusionStep 𝒜 st).tail_strict
  rejected := (rosenthalFusionStep 𝒜 st).rejected

private def rosenthalFusionInitial
    (𝒜 : List ℕ → Prop) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hrej : rosenthalRejects 𝒜 [] φ) : RosenthalFusionState 𝒜 where
  chosen := []
  tail := φ
  tail_strict := hφ
  rejected := by
    intro s hs
    simp only [List.sublists_nil, List.mem_singleton] at hs
    simpa [hs] using hrej

private noncomputable def rosenthalFusionStates
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) :
    RosenthalFusionState 𝒜 :=
  (rosenthalFusionNext 𝒜)^[n] st

private noncomputable def rosenthalFusionPoints
    (𝒜 : List ℕ → Prop) (st : RosenthalFusionState 𝒜) (n : ℕ) : ℕ :=
  (rosenthalFusionStep 𝒜 (rosenthalFusionStates 𝒜 st n)).point

private theorem rosenthal_open_ramsey
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

private def rosenthalPairsHold {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) : List ℕ → Prop
  | a :: b :: s => R k a b ∧ rosenthalPairsHold R k s
  | _ => True

private theorem rosenthal_pairsHold_initial_even {K : Type*}
    (R : K → ℕ → ℕ → Prop) (k : K) (φ : ℕ → ℕ) :
    ∀ N, rosenthalPairsHold R k (rosenthalInitialSegment φ (2 * N)) ↔
      ∀ j < N, R k (φ (2 * j)) (φ (2 * j + 1)) := by
  intro N
  induction N generalizing φ with
  | zero => simp [rosenthalInitialSegment, rosenthalPairsHold]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        rosenthal_initialSegment_succ, rosenthal_initialSegment_succ]
      simp only [rosenthalPairsHold]
      rw [ih]
      constructor
      · rintro ⟨hzero, htail⟩ j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simpa [rosenthalTail] using hzero
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
          have hi : i < N := by omega
          change R k (φ (2 * (i + 1))) (φ (2 * (i + 1) + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using htail i hi
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [rosenthalTail] using h 0 (Nat.zero_lt_succ N)
        · intro i hi
          change R k (φ (2 * i + 1 + 1)) (φ (2 * i + 1 + 1 + 1))
          simpa [rosenthalTail, mul_add, add_assoc] using h (i + 1) (by omega)

private def rosenthalPaired {K : Type*}
    (R : K → ℕ → ℕ → Prop) (φ : ℕ → ℕ) : Prop :=
  ∃ k, ∀ n, R k (φ (2 * n)) (φ (2 * n + 1))

private def rosenthalPairObstruction {K : Type*}
    (R : K → ℕ → ℕ → Prop) (s : List ℕ) : Prop :=
  ∃ N, s.length = 2 * N ∧ ¬∃ k, rosenthalPairsHold R k s

private theorem rosenthal_closed_ramsey
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

private theorem rosenthal_finite_closed_ramsey
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

private def rosenthalPairLift (η : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * η (n / 2) + n % 2

private def rosenthalCellPair {K 𝕜 : Type*} [Dist 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜) (k : K) (i j : ℕ) : Prop :=
  dist (f i k) u ≤ delta ∧ dist (f j k) v ≤ delta

private def rosenthalGap {K alpha : Type*} [Dist alpha]
    (f : ℕ → K → alpha) (epsilon : ℝ) (k : K) (i j : ℕ) : Prop :=
  epsilon ≤ dist (f i k) (f j k)

private theorem rosenthal_exists_uniform_cell_pair
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

private def rosenthalAssignmentIndices (P : Finset ℕ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    if n / 2 ∈ P then 3 * (n / 2) + 1 else 3 * (n / 2)
  else
    if n / 2 ∈ P then 3 * (n / 2) + 2 else 3 * (n / 2) + 1

private abbrev RosenthalDualBall (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  {g : WeakDual 𝕜 E //
    WeakDual.toStrongDual g ∈ Metric.closedBall (0 : StrongDual 𝕜 E) 1}

private noncomputable instance rosenthalDualBallCompact
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    CompactSpace (RosenthalDualBall 𝕜 E) :=
  isCompact_iff_compactSpace.mp
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1)

private instance rosenthalDualBallNonempty
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Nonempty (RosenthalDualBall 𝕜 E) :=
  ⟨⟨0, by simp [Metric.mem_closedBall]⟩⟩

private noncomputable def rosenthalDualBallStrong
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : RosenthalDualBall 𝕜 E) : StrongDual 𝕜 E :=
  WeakDual.toStrongDual g.1

private noncomputable def rosenthalDualEval
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) : 𝕜 :=
  g.1 (x n)

/-- `y : ℕ → E` has a uniform `ℓ¹` lower bound when some `c > 0` satisfies
`‖∑ i, a i • y i‖ ≥ c * ∑ i, ‖a i‖` for every finitely supported `a : ℕ →₀ 𝕜`. -/
def HasUniformL1LowerBound {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (y : ℕ → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ →₀ 𝕜),
    ‖∑ i ∈ a.support, a i • y i‖ ≥ c * ∑ i ∈ a.support, ‖a i‖

private structure RosenthalSequenceState where
  seq : ℕ → ℕ
  strict : StrictMono seq

private theorem rosenthal_pointwiseCauchy_or_uniformlySeparated
    {K α : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [PseudoMetricSpace α] (f : ℕ → K → α) (hf : ∀ n, Continuous (f n)) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : K, ∀ ε : ℝ, 0 < ε →
        ∃ N, ∀ m n, N ≤ m → N ≤ n → dist (f (φ m) k) (f (φ n) k) < ε := by
  classical
  by_cases hsep : ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ θ : ℕ → ℕ, StrictMono θ → rosenthalPaired (rosenthalGap f ε) (φ ∘ θ)
  · exact Or.inl hsep
  · have heps : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := by
      intro n
      positivity
    have hstep : ∀ (n : ℕ) (st : RosenthalSequenceState),
        ∃ next : RosenthalSequenceState,
          Set.range next.seq ⊆ Set.range st.seq ∧
          (∀ j, st.seq 0 < next.seq j) ∧
          ∀ θ : ℕ → ℕ, StrictMono θ →
            ¬rosenthalPaired (rosenthalGap f (1 / ((n : ℝ) + 1))) (next.seq ∘ θ) := by
      intro n st
      let δ : ℝ := 1 / ((n : ℝ) + 1)
      let tail := rosenthalTail st.seq
      have htail : StrictMono tail := rosenthal_tail_strictMono st.strict
      have hclosed : ∀ i j, IsClosed {k | rosenthalGap f δ k i j} := by
        intro i j
        exact isClosed_le continuous_const ((hf i).dist (hf j))
      obtain ⟨ψ, hψ, hψrange, hhom⟩ := rosenthal_closed_ramsey
        (rosenthalGap f δ) hclosed htail
      have hrange : Set.range ψ ⊆ Set.range st.seq :=
        hψrange.trans (Set.range_comp_subset_range (fun q => q + 1) st.seq)
      have habove : ∀ j, st.seq 0 < ψ j := by
        intro j
        obtain ⟨q, hq⟩ := hψrange ⟨j, rfl⟩
        rw [← hq]
        exact st.strict (Nat.zero_lt_succ q)
      rcases hhom with hpos | hneg
      · exfalso
        apply hsep
        exact ⟨δ, heps n, ψ, hψ, hpos⟩
      · exact ⟨⟨ψ, hψ⟩, hrange, habove, hneg⟩
    choose step hstep_range hstep_above hstep_nogap using hstep
    let states : ℕ → RosenthalSequenceState := fun n =>
      Nat.rec ⟨id, strictMono_id⟩ (fun n st => step n st) n
    have hstates_zero : states 0 = ⟨id, strictMono_id⟩ := rfl
    have hstates_succ : ∀ n, states (n + 1) = step n (states n) := fun n => rfl
    let φ : ℕ → ℕ := fun n => (states n).seq 0
    have hφ : StrictMono φ := by
      apply strictMono_nat_of_lt_succ
      intro n
      change (states n).seq 0 < (states (n + 1)).seq 0
      rw [hstates_succ]
      exact hstep_above n (states n) 0
    have hstates_range : ∀ {m n : ℕ}, m ≤ n →
        Set.range (states n).seq ⊆ Set.range (states m).seq := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact Set.Subset.rfl
      | succ n hmn ih =>
          rw [hstates_succ]
          exact (hstep_range n (states n)).trans ih
    refine Or.inr ⟨φ, hφ, ?_⟩
    intro k ε hε
    obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
    have hno := hstep_nogap q (states q)
    rw [← hstates_succ q] at hno
    have hbase := rosenthal_eventually_close_of_no_gap_paired
      f (heps q) hno k
    let tailφ : ℕ → ℕ := fun j => φ (q + 1 + j)
    have htailφ : StrictMono tailφ :=
      hφ.comp fun _ _ h => Nat.add_lt_add_left h (q + 1)
    have htailrange : Set.range tailφ ⊆ Set.range (states (q + 1)).seq := by
      rintro _ ⟨j, rfl⟩
      apply hstates_range (Nat.le_add_right (q + 1) j)
      exact ⟨0, rfl⟩
    obtain ⟨η, hη, htailcomp⟩ := rosenthal_exists_indices_of_range_subset
      (states (q + 1)).strict htailφ htailrange
    obtain ⟨N, hN⟩ := hbase
    refine ⟨q + 1 + N, ?_⟩
    intro m n hm hn
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
    have hηm : N ≤ η (N + m') :=
      (Nat.le_add_right N m').trans (StrictMono.id_le hη (N + m'))
    have hηn : N ≤ η (N + n') :=
      (Nat.le_add_right N n').trans (StrictMono.id_le hη (N + n'))
    have hclose := hN (η (N + m')) (η (N + n')) hηm hηn
    have hm_eq : tailφ (N + m') = (states (q + 1)).seq (η (N + m')) := by
      simpa only [Function.comp_apply] using congrFun htailcomp (N + m')
    have hn_eq : tailφ (N + n') = (states (q + 1)).seq (η (N + n')) := by
      simpa only [Function.comp_apply] using congrFun htailcomp (N + n')
    rw [← hm_eq, ← hn_eq] at hclose
    simpa [tailφ, Nat.add_assoc] using lt_trans hclose hq

/--
Every bounded sequence `x` in a Banach space over `𝕜 = ℝ` or `ℂ` has a strictly increasing
subsequence `φ` such that `x ∘ φ` is either weakly Cauchy (`f (x (φ n))` Cauchy for every `f : E
→L[𝕜] 𝕜`) or has a uniform `ℓ¹` lower bound. Source: H. P. Rosenthal,
A Characterization of Banach Spaces Containing l1, PNAS 71 (1974), 2411–2413,
DOI 10.1073/pnas.71.6.2411, ℓ¹ dichotomy theorem; Bourgain et al., extensions; Lean states
`RCLike` Banach bounded `Set.range` dichotomy with `StrictMono φ` and `HasUniformL1LowerBound`
defined via `ℕ →₀ 𝕜` finitely supported coefficients.

Proves `Wanted` entry `rosenthal_l1`.

Proof: We use the Nash-Williams/Galvin-Prikry Ramsey route, following Rosenthal's 1974 theorem,
Albiac and Kalton, Sections 10.1–10.2, and Farahat's 1974 proof.
-/
theorem rosenthal_l1
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ),
      (∀ (f : E →L[𝕜] 𝕜) (ε : ℝ), 0 < ε →
        ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖f (x (φ m)) - f (x (φ n))‖ < ε) ∨
      HasUniformL1LowerBound (𝕜 := 𝕜) (x ∘ φ) := by
  let eval : ℕ → RosenthalDualBall 𝕜 E → 𝕜 :=
    rosenthalDualEval (𝕜 := 𝕜) x
  have heval : ∀ n, Continuous (eval n) :=
    rosenthal_dualEval_continuous (𝕜 := 𝕜) x
  obtain ⟨B, hB⟩ := rosenthal_dualEval_bounded (𝕜 := 𝕜) x hx
  rcases rosenthal_pointwiseCauchy_or_uniformlySeparated eval heval with hsep | hcauchy
  · obtain ⟨epsilon, hepsilon, φ, hφ, hseparated⟩ := hsep
    obtain ⟨u, v, hcenters, ψ, hψ, hψrange, hcells⟩ :=
      rosenthal_exists_uniform_cell_pair eval heval B epsilon (epsilon / 64)
        (by positivity) hB hφ hseparated
    obtain ⟨χ, hχ, hχrange, hassign⟩ :=
      rosenthal_cell_pair_assignments eval (epsilon / 64) u v hψ hcells
    refine ⟨χ, hχ, Or.inr ?_⟩
    apply rosenthal_uniform_lower_bound_of_assignments (x ∘ χ)
      epsilon hepsilon u v hcenters
    intro P Q hPQ
    obtain ⟨g, hgu, hgv⟩ := hassign P Q hPQ
    exact ⟨g, by
      simpa [eval, rosenthalDualEval, Function.comp_def] using hgu, by
      simpa [eval, rosenthalDualEval, Function.comp_def] using hgv⟩
  · obtain ⟨φ, hφ, hcauchy⟩ := hcauchy
    refine ⟨φ, hφ, Or.inl ?_⟩
    apply rosenthal_weakCauchy_of_dualBall x φ
    simpa [eval] using hcauchy

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
