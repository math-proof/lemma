/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Structure.Analysis.NormedSpace.RosenthalL1.Part2
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_pointwiseCauchy_or_uniformlySeparated
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
public theorem rosenthal_l1
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

end FunctionalAnalysis.RosenthalL1Wanted
