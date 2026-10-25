/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Def.Combinatorics.Additive.Sarkozy.Part5


namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- The shift moves basis vectors forward by one. -/
theorem sarkozyShiftIso_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (a : ℤ) :
    (sarkozyShiftIso γ hsymm hpos) (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (a + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  have h1 : ((sarkozyShiftIso γ hsymm hpos)
      (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ) : ℤ →₀ ℝ)
      = Finsupp.mapDomain (fun i : ℤ => i + 1) (Finsupp.single a 1) := rfl
  have hgoal : ((sarkozyShiftIso γ hsymm hpos)
      (((Finsupp.single a 1 : ℤ →₀ ℝ)) : sarkozyToep γ) : ℤ →₀ ℝ)
      = Finsupp.single (a + 1) 1 := by
    rw [h1, Finsupp.mapDomain_single]
  exact hgoal

/-- Iterates of the shift move the zeroth basis vector forward (N5). -/
theorem sarkozyShiftIso_iterate_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (m : ℕ) :
    (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (m : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  induction m with
  | zero =>
    rw [Function.iterate_zero, Nat.cast_zero]
    rfl
  | succ m ih =>
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hstep : (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m.succ]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
        = (⇑(sarkozyShiftIso γ hsymm hpos))
          (((⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
            (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ))) :=
      Function.iterate_succ_apply' _ _ _
    have hbridge := congrArg (fun n : ℕ => (⇑(sarkozyShiftIso γ hsymm hpos)) ^[n]
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ))
      (Nat.succ_eq_add_one m)
    have hsingle := sarkozyShiftIso_single γ hsymm hpos ((m : ℤ))
    have hinner : (⇑(sarkozyShiftIso γ hsymm hpos))
        (((⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
          (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)))
        = (((Finsupp.single ((m : ℤ) + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) :=
      Eq.trans (congrArg (⇑(sarkozyShiftIso γ hsymm hpos)) ih) hsingle
    have hchain : (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m.succ]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
        = (((Finsupp.single ((m : ℤ) + 1) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) :=
      Eq.trans hstep hinner
    rw [hcast]
    exact Eq.trans hbridge.symm hchain

/-- Powers of the shift move the zeroth basis vector forward (N5). -/
theorem sarkozyShiftIso_pow_single (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) (m : ℕ) :
    ((sarkozyShiftIso γ hsymm hpos) ^ m)
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (((Finsupp.single (m : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
  have hiter := sarkozyShiftIso_iterate_single γ hsymm hpos m
  have hcoe := @LinearIsometry.coe_pow ℝ (sarkozyToep γ) inferInstance
    (sarkozyToep_seminormed γ hsymm hpos) (sarkozyToep_module)
    (sarkozyShiftIso γ hsymm hpos) m
  have hrewrite : ((sarkozyShiftIso γ hsymm hpos) ^ m)
      (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ)
      = (⇑(sarkozyShiftIso γ hsymm hpos)) ^[m]
        (((Finsupp.single 0 1 : ℤ →₀ ℝ)) : sarkozyToep γ) := by
    rw [hcoe]
  rw [hrewrite]
  exact hiter

/-- GNS dilation: isometric shift on the Hilbert completion with correlations γ (N6). -/
theorem sarkozy_dilation (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E)
      (_ : CompleteSpace E),
      ∃ (U : E →ₗᵢ[ℝ] E) (v : E), ∀ m n : ℕ,
        inner ℝ ((U ^ m) v) ((U ^ n) v) = γ ((m : ℤ) - n) := by
  let instN : SeminormedAddCommGroup (sarkozyToep γ) :=
    sarkozyToep_seminormed γ hsymm hpos
  let instI : InnerProductSpace ℝ (sarkozyToep γ) :=
    sarkozyToep_innerProd γ hsymm hpos
  set S : (sarkozyToep γ) →ₗᵢ[ℝ] (sarkozyToep γ) :=
    sarkozyShiftIso γ hsymm hpos with hS
  set T : UniformSpace.Completion (sarkozyToep γ) →L[ℝ]
      UniformSpace.Completion (sarkozyToep γ) :=
    S.toContinuousLinearMap.completion with hT
  have hTnorm : ∀ x : UniformSpace.Completion (sarkozyToep γ), ‖T x‖ = ‖x‖ := by
    intro x
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq (Continuous.norm T.continuous) continuous_norm) (fun a => ?_)
    rw [ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact S.norm_map a
  set U : UniformSpace.Completion (sarkozyToep γ) →ₗᵢ[ℝ]
      UniformSpace.Completion (sarkozyToep γ) :=
    ⟨T.toLinearMap, hTnorm⟩ with hU
  have hUcoe : ∀ x : sarkozyToep γ, U (↑x) = ↑(S x) := fun x =>
    ContinuousLinearMap.completion_apply_coe _ x
  have hcomm : ∀ (m : ℕ) (x : sarkozyToep γ), (U ^ m) (↑x) = ↑((S ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      have e1 : (U ^ (m + 1)) (↑x) = (U ^ m) (U (↑x)) := by
        rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply]
      have e2 : ((S ^ (m + 1)) x : sarkozyToep γ) = (S ^ m) (S x) := by
        rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply]
      rw [e1, hUcoe, ih, e2]
  set s0 : sarkozyToep γ :=
    (((Finsupp.single (0 : ℤ) 1 : ℤ →₀ ℝ)) : sarkozyToep γ) with hs0
  refine ⟨UniformSpace.Completion (sarkozyToep γ), inferInstance, inferInstance,
    inferInstance, U, (↑s0 : UniformSpace.Completion (sarkozyToep γ)), ?_⟩
  intro m n
  rw [hcomm, hcomm, UniformSpace.Completion.inner_coe,
    sarkozyShiftIso_pow_single γ hsymm hpos m,
    sarkozyShiftIso_pow_single γ hsymm hpos n]
  exact sarkozyToepInnerAux_single γ (m : ℤ) (n : ℤ)

/-- Correlation limit along a density subsequence (N4). -/
theorem sarkozy_corr_limit (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hfreq : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ))
    (hNSD : ∀ a b k : ℕ, a ∈ A → b ∈ A → 0 < k → a < b → b ≠ a + k * k) :
    ∃ γ : ℤ → ℝ, (∀ d : ℤ, γ (-d) = γ d)
      ∧ (∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
        0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))
      ∧ (∀ k : ℕ, 0 < k → γ ((k : ℤ) * k) = 0)
      ∧ (∀ L : ℕ, 0 < L → (L : ℝ) ^ 2 * δ ^ 2 ≤
        ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h')) := by
  have hfreq' : ∀ k : ℕ, ∃ N : ℕ, k + 1 ≤ N ∧
      δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ) := fun k => hfreq (k + 1)
  choose Nseq hNseq using hfreq'
  have hNpos : ∀ k : ℕ, (0 : ℝ) < (Nseq k : ℝ) := by
    intro k
    have h1 : 0 < Nseq k :=
      lt_of_lt_of_le (Nat.zero_lt_succ k) (hNseq k).1
    exact_mod_cast h1
  have hRle : ∀ k : ℕ, ∀ d : ℤ,
      ((sarkozyCorr A (Nseq k) d : ℕ) : ℝ) ≤ (Nseq k : ℝ) := by
    intro k d
    have h := le_trans (sarkozy_corr_le_card A (Nseq k) d) (sarkozy_card_le A (Nseq k))
    exact_mod_cast h
  have hcompact : IsCompact (Set.univ.pi (fun _ : ℤ => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hmem : ∀ k : ℕ, (fun d : ℤ => ((sarkozyCorr A (Nseq k) d : ℕ) : ℝ) / (Nseq k : ℝ))
      ∈ Set.univ.pi (fun _ : ℤ => Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [Set.mem_univ_pi]
    intro d
    rw [Set.mem_Icc]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one (hNpos k)]
      exact hRle k d
  obtain ⟨γ, -, φ, hφmono, hφlim⟩ := hcompact.tendsto_subseq hmem
  have hpt : ∀ d : ℤ, Filter.Tendsto
      (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
      Filter.atTop (nhds (γ d)) :=
    fun d => (tendsto_pi_nhds.mp hφlim) d
  have hga : ∀ d : ℤ, γ (-d) = γ d := by
    intro d
    have heq : ∀ k : ℕ, ((sarkozyCorr A (Nseq (φ k)) (-d) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)
        = ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ) := by
      intro k
      rw [sarkozy_corr_neg]
    have h1 := hpt (-d)
    have h2 := hpt d
    rw [show (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) (-d) : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
        = (fun k : ℕ => ((sarkozyCorr A (Nseq (φ k)) d : ℕ) : ℝ) / (Nseq (φ k) : ℝ))
      from funext heq] at h1
    exact tendsto_nhds_unique h1 h2
  have hgb : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j) := by
    intro s c
    have hnn : ∀ k : ℕ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      have hN1k := sarkozy_corr_nonneg A (Nseq (φ k)) s (fun d => d) c
      have hfactor : (∑ i ∈ s, ∑ j ∈ s, c i * c j *
            (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
          = ((Nseq (φ k) : ℝ))⁻¹ * (∑ i ∈ s, ∑ j ∈ s, c i * c j *
            ((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_inv_mul]
        ring
      rw [hfactor]
      exact mul_nonneg (inv_nonneg.mpr (hNpos (φ k)).le) hN1k
    have hlim : Filter.Tendsto (fun k : ℕ => ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (((sarkozyCorr A (Nseq (φ k)) (i - j) : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
        Filter.atTop
        (nhds (∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j))) := by
      refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
      exact tendsto_const_nhds.mul (hpt (i - j))
    exact ge_of_tendsto' hlim hnn
  have hgc : ∀ k : ℕ, 0 < k → γ ((k : ℤ) * k) = 0 := by
    intro k hk
    have h0 : ∀ n : ℕ, ((sarkozyCorr A (Nseq (φ n)) ((k : ℤ) * k) : ℕ) : ℝ)
        / (Nseq (φ n) : ℝ) = 0 := by
      intro n
      rw [sarkozy_corr_sq_eq_zero A (Nseq (φ n)) k hk hNSD]
      simp
    have hlim := hpt ((k : ℤ) * k)
    have hlim0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (γ ((k : ℤ) * k))) :=
      hlim.congr h0
    have h00 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique hlim0 h00
  have hNseqTop : Filter.Tendsto Nseq Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun k hk => ?_⟩
    have hm := (hNseq k).1
    omega
  have hcomp : Filter.Tendsto (Nseq ∘ φ) Filter.atTop Filter.atTop :=
    hNseqTop.comp hφmono.tendsto_atTop
  have hgd : ∀ L : ℕ, 0 < L → (L : ℝ) ^ 2 * δ ^ 2 ≤
      ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h') := by
    intro L hL
    have hC : ∀ k : ℕ, δ * (Nseq (φ k) : ℝ)
        ≤ ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) := by
      intro k
      have h := (hNseq (φ k)).2
      rwa [← sarkozyFin_card] at h
    have hN3 : ∀ k : ℕ, (L : ℝ) ^ 2 * ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2
        ≤ ((Nseq (φ k) : ℝ) + (L : ℝ)) * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          ((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ)) :=
      fun k => sarkozy_corr_fejer_lower_bound A (Nseq (φ k)) L
    have hCsq : ∀ k : ℕ, (δ * (Nseq (φ k) : ℝ)) ^ 2
        ≤ ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2 := by
      intro k
      exact pow_le_pow_left₀ (mul_nonneg hδ.le (Nat.cast_nonneg _)) (hC k) 2
    have hdiv : ∀ k : ℕ, (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          ((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ)) / (Nseq (φ k) : ℝ)
        = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h' _
      rw [div_eq_mul_inv]
    have hle : ∀ k : ℕ, ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ)) / ((Nseq (φ k) : ℝ) + (L : ℝ))
        ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)) := by
      intro k
      have hMpos : (0 : ℝ) < (Nseq (φ k) : ℝ) := hNpos (φ k)
      have hMLpos : (0 : ℝ) < (Nseq (φ k) : ℝ) + (L : ℝ) := by
        have hnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
        linarith [hNpos (φ k)]
      rw [← hdiv k, div_le_div_iff₀ hMLpos hMpos]
      have h2 : (L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ) * (Nseq (φ k) : ℝ)
          = (L : ℝ) ^ 2 * (δ * (Nseq (φ k) : ℝ)) ^ 2 := by
        ring
      rw [h2]
      calc (L : ℝ) ^ 2 * (δ * (Nseq (φ k) : ℝ)) ^ 2
            ≤ (L : ℝ) ^ 2 * ((((sarkozyFin A (Nseq (φ k))).card : ℕ)) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (hCsq k) (sq_nonneg _)
        _ ≤ ((Nseq (φ k) : ℝ) + (L : ℝ)) * _ := hN3 k
        _ = _ * ((Nseq (φ k) : ℝ) + (L : ℝ)) := mul_comm _ _
    have hLBlim : Filter.Tendsto
        (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ)) / ((Nseq (φ k) : ℝ) + (L : ℝ)))
        Filter.atTop (nhds ((L : ℝ) ^ 2 * δ ^ 2)) := by
      have hfrac : Filter.Tendsto
          (fun k : ℕ => (Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ)))
          Filter.atTop (nhds 1) :=
        (tendsto_natCast_div_add_atTop (L : ℝ)).comp hcomp
      have hmul : Filter.Tendsto
          (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2) * ((Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ))))
          Filter.atTop (nhds (((L : ℝ) ^ 2 * δ ^ 2) * 1)) :=
        tendsto_const_nhds.mul hfrac
      rw [mul_one] at hmul
      have hfun : (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2 * (Nseq (φ k) : ℝ))
            / ((Nseq (φ k) : ℝ) + (L : ℝ)))
          = (fun k : ℕ => ((L : ℝ) ^ 2 * δ ^ 2)
            * ((Nseq (φ k) : ℝ) / ((Nseq (φ k) : ℝ) + (L : ℝ)))) := by
        apply funext
        intro k
        ring
      rw [hfun]
      exact hmul
    have hSlim : Filter.Tendsto
        (fun k : ℕ => ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          (((sarkozyCorr A (Nseq (φ k)) ((h : ℤ) - h') : ℕ) : ℝ) / (Nseq (φ k) : ℝ)))
        Filter.atTop (nhds (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h : ℤ) - h'))) := by
      refine tendsto_finsetSum _ (fun h _ => tendsto_finsetSum _ (fun h' _ => ?_))
      exact hpt ((h : ℤ) - h')
    have hfin := le_of_tendsto_of_tendsto' hLBlim hSlim hle
    exact hfin
  exact ⟨γ, hga, hgb, hgc, hgd⟩

/-- Shift-difference identity for range sums (N7 helper). -/
theorem sarkozy_sum_shift_diff {G : Type*} [AddCommGroup G] (g : ℕ → G)
    (M h : ℕ) :
    (∑ n ∈ Finset.range M, g (n + h)) - (∑ n ∈ Finset.range M, g n)
      = (∑ k ∈ Finset.range h, g (M + k)) - (∑ k ∈ Finset.range h, g k) := by
  have hadd1 := Finset.sum_range_add g h M
  have hadd2 := Finset.sum_range_add g M h
  have hMH : h + M = M + h := add_comm _ _
  rw [hMH] at hadd1
  have hconv : (∑ x ∈ Finset.range M, g (h + x))
      = (∑ n ∈ Finset.range M, g (n + h)) :=
    Finset.sum_congr rfl (fun n _ => by rw [add_comm h n])
  have key : (∑ n ∈ Finset.range M, g n) + (∑ k ∈ Finset.range h, g (M + k))
      = (∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g (n + h)) := by
    rw [← hconv, ← hadd1, ← hadd2]
  calc (∑ n ∈ Finset.range M, g (n + h)) - (∑ n ∈ Finset.range M, g n)
        = ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g (n + h)))
          - ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g n)) := by
        abel
    _ = ((∑ n ∈ Finset.range M, g n) + (∑ k ∈ Finset.range h, g (M + k)))
          - ((∑ k ∈ Finset.range h, g k) + (∑ n ∈ Finset.range M, g n)) := by
        rw [← key]
    _ = (∑ k ∈ Finset.range h, g (M + k)) - (∑ k ∈ Finset.range h, g k) := by
        abel

/-- Van der Corput shift bound (N7(i)): averaging over shifts barely moves the sum. -/
theorem sarkozy_vdc_avg_shift {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (M H : ℕ) :
    ‖(H : ℝ) • ∑ n ∈ Finset.range M, x n
      - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
      ≤ (H : ℝ)^2 * C := by
  have hdiff : ∀ h : ℕ, ‖(∑ n ∈ Finset.range M, x n)
        - (∑ n ∈ Finset.range M, x (n + h))‖ ≤ 2 * (h : ℝ) * C := by
    intro h
    have hkey := sarkozy_sum_shift_diff x M h
    have heq : (∑ n ∈ Finset.range M, x n) - (∑ n ∈ Finset.range M, x (n + h))
        = (∑ k ∈ Finset.range h, x k) - (∑ k ∈ Finset.range h, x (M + k)) := by
      calc (∑ n ∈ Finset.range M, x n) - (∑ n ∈ Finset.range M, x (n + h))
            = -((∑ n ∈ Finset.range M, x (n + h))
              - (∑ n ∈ Finset.range M, x n)) := by abel
        _ = -((∑ k ∈ Finset.range h, x (M + k))
              - (∑ k ∈ Finset.range h, x k)) := by rw [hkey]
        _ = (∑ k ∈ Finset.range h, x k)
              - (∑ k ∈ Finset.range h, x (M + k)) := by abel
    rw [heq]
    calc ‖(∑ k ∈ Finset.range h, x k) - (∑ k ∈ Finset.range h, x (M + k))‖
          ≤ ‖∑ k ∈ Finset.range h, x k‖ + ‖∑ k ∈ Finset.range h, x (M + k)‖ :=
          norm_sub_le _ _
      _ ≤ (∑ k ∈ Finset.range h, ‖x k‖)
          + (∑ k ∈ Finset.range h, ‖x (M + k)‖) :=
          add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
      _ ≤ (∑ _k ∈ Finset.range h, C) + (∑ _k ∈ Finset.range h, C) := by
          apply add_le_add <;> exact Finset.sum_le_sum (fun k _ => hx _)
      _ = 2 * (h : ℝ) * C := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hgaussR : ∀ H : ℕ, 2 * (∑ h ∈ Finset.range H, (h : ℝ))
      = (H : ℝ) * ((H : ℝ) - 1) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      linear_combination ih
  have hpair : 2 * (∑ h ∈ Finset.range H, (h : ℝ)) ≤ (H : ℝ)^2 := by
    rw [hgaussR H]
    have hnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    have heq : (H : ℝ) * ((H : ℝ) - 1) = (H : ℝ)^2 - (H : ℝ) := by ring
    rw [heq]
    linarith
  have hHsmul : ((H : ℝ) • ∑ n ∈ Finset.range M, x n)
      = ∑ _h ∈ Finset.range H, (∑ n ∈ Finset.range M, x n) := by
    rw [Finset.sum_const, Finset.card_range]
    exact Nat.cast_smul_eq_nsmul ℝ H _
  have hswap : (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
      = ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range M, x (n + h) := Finset.sum_comm
  have hD : (H : ℝ) • (∑ n ∈ Finset.range M, x n)
        - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)
      = ∑ h ∈ Finset.range H, ((∑ n ∈ Finset.range M, x n)
        - (∑ n ∈ Finset.range M, x (n + h))) := by
    rw [hHsmul, hswap, ← Finset.sum_sub_distrib]
  rw [hD]
  calc ‖∑ h ∈ Finset.range H, ((∑ n ∈ Finset.range M, x n)
          - (∑ n ∈ Finset.range M, x (n + h)))‖
        ≤ ∑ h ∈ Finset.range H, ‖(∑ n ∈ Finset.range M, x n)
          - (∑ n ∈ Finset.range M, x (n + h))‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.range H, (2 * (h : ℝ) * C) :=
        Finset.sum_le_sum (fun h _ => hdiff h)
    _ = 2 * C * (∑ h ∈ Finset.range H, (h : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring
    _ ≤ (H : ℝ)^2 * C := by
        calc 2 * C * (∑ h ∈ Finset.range H, (h : ℝ))
            = (2 * (∑ h ∈ Finset.range H, (h : ℝ))) * C := by ring
          _ ≤ (H : ℝ)^2 * C := mul_le_mul_of_nonneg_right hpair hC

/-- Van der Corput square bound (N7(ii)): the double-shifted sum via correlations. -/
theorem sarkozy_vdc_sq_bound {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (M H : ℕ) :
    ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖^2
      ≤ (M : ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M,
        inner ℝ (x (n + h)) (x (n + h'))) := by
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range M)
    (f := fun n => ‖∑ h ∈ Finset.range H, x (n + h)‖)
  rw [Finset.card_range] at h2
  have hnorm : ∀ n : ℕ, ‖∑ h ∈ Finset.range H, x (n + h)‖^2
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        inner ℝ (x (n + h)) (x (n + h')) := by
    intro n
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl
    intro h _
    exact inner_sum _ _ _
  have hswap : (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H,
        ∑ h' ∈ Finset.range H, inner ℝ (x (n + h)) (x (n + h')))
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H, ∑ n ∈ Finset.range M,
        inner ℝ (x (n + h)) (x (n + h')) := by
    trans ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range M, ∑ h' ∈ Finset.range H,
      inner ℝ (x (n + h)) (x (n + h'))
    · exact Finset.sum_comm
    · apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
  calc ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖^2
      ≤ (∑ n ∈ Finset.range M, ‖∑ h ∈ Finset.range H, x (n + h)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (M : ℝ) * (∑ n ∈ Finset.range M,
          ‖∑ h ∈ Finset.range H, x (n + h)‖^2) := h2
    _ = (M : ℝ) * (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H,
          ∑ h' ∈ Finset.range H, inner ℝ (x (n + h)) (x (n + h'))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        exact hnorm n
    _ = (M : ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h'))) := by
        rw [hswap]

/-- Van der Corput correlation stability (N7(iii)): shifting both slots nearly preserves
the correlation sum. -/
theorem sarkozy_vdc_corr_stable {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (M h h' : ℕ) (hle : h' ≤ h) :
    |∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h'))
      - ∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n)|
      ≤ 2 * (h' : ℝ) * C^2 := by
  have key := sarkozy_sum_shift_diff
    (fun m => inner ℝ (x ((h - h') + m)) (x m)) M h'
  have e1 : (∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h')))
      = ∑ n ∈ Finset.range M,
        (fun m => inner ℝ (x ((h - h') + m)) (x m)) (n + h') := by
    apply Finset.sum_congr rfl
    intro n _
    have hnn : n + h = (h - h') + (n + h') := by omega
    rw [hnn]
  have e2 : (∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n))
      = ∑ n ∈ Finset.range M,
        (fun m => inner ℝ (x ((h - h') + m)) (x m)) n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [add_comm n (h - h')]
  have hdecomp : (∑ n ∈ Finset.range M, inner ℝ (x (n + h)) (x (n + h')))
        - (∑ n ∈ Finset.range M, inner ℝ (x (n + (h - h'))) (x n))
      = (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))
        - (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k) := by
    rw [e1, e2]
    exact key
  have hterm : ∀ m, |(fun m => inner ℝ (x ((h - h') + m)) (x m)) m| ≤ C^2 := by
    intro m
    calc |(fun m => inner ℝ (x ((h - h') + m)) (x m)) m|
          ≤ ‖x ((h - h') + m)‖ * ‖x m‖ := abs_real_inner_le_norm _ _
      _ ≤ C * C := mul_le_mul (hx _) (hx _) (norm_nonneg _) hC
      _ = C^2 := by ring
  have habs : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := by
    intro X Y
    calc |X - Y| = |X + (-Y)| := by rw [sub_eq_add_neg]
      _ ≤ |X| + |-Y| := abs_add_le _ _
      _ = |X| + |Y| := by rw [abs_neg]
  rw [hdecomp]
  calc |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))
        - (∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k)|
      ≤ |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k))|
        + |(∑ k ∈ Finset.range h',
          (fun m => inner ℝ (x ((h - h') + m)) (x m)) k)| := habs _ _
    _ ≤ (∑ k ∈ Finset.range h',
          |(fun m => inner ℝ (x ((h - h') + m)) (x m)) (M + k)|)
        + (∑ k ∈ Finset.range h',
          |(fun m => inner ℝ (x ((h - h') + m)) (x m)) k|) :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _k ∈ Finset.range h', C^2) + (∑ _k ∈ Finset.range h', C^2) := by
        apply add_le_add <;> exact Finset.sum_le_sum (fun k _ => hterm _)
    _ = 2 * (h' : ℝ) * C^2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Hilbert-space van der Corput lemma (N8): vanishing lag-correlations kill the mean. -/
theorem sarkozy_vdc_tendsto {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C)
    (hcorr : ∀ d : ℕ, 1 ≤ d → Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n + d)) (x n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun (M : ℕ) => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0:ℝ) < ε^2 := by positivity
  obtain ⟨H, hH1, hHC⟩ : ∃ H : ℕ, 1 ≤ H ∧ C^2 / (H:ℝ) ≤ ε^2 / 16 := by
    refine ⟨Nat.floor (16 * C^2 / ε^2) + 1, Nat.le_add_left 1 _, ?_⟩
    have hHpos : (0:ℝ) < ((((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    rw [div_le_div_iff₀ hHpos (by norm_num : (0:ℝ) < 16)]
    have hfloor : 16 * C^2 / ε^2 ≤ (((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ) : ℝ)) := by
      have hfl := Nat.lt_floor_add_one (16 * C^2 / ε^2)
      have hcast : ((((Nat.floor (16 * C^2 / ε^2) + 1 : ℕ))) : ℝ)
          = ((Nat.floor (16 * C^2 / ε^2) : ℝ)) + 1 := by push_cast; ring
      rw [hcast]
      linarith
    calc C^2 * 16 = (16 * C^2 / ε^2) * ε^2 := by
            rw [div_mul_cancel₀ _ (ne_of_gt hε2)]; ring
      _ ≤ _ * ε^2 := mul_le_mul_of_nonneg_right hfloor hε2.le
      _ = ε^2 * _ := by ring
  have hHpos : (0:ℝ) < (H:ℝ) := Nat.cast_pos.mpr (by omega)
  have hHne : (H:ℝ) ≠ 0 := ne_of_gt hHpos
  have hK0pos : (0:ℝ) < ε^2/16 := by linarith [hε2]
  obtain ⟨NM1, hNM1⟩ := exists_nat_gt (1 / (ε^2/(32*((H:ℝ)*C^2+1))))
  obtain ⟨NM2, hNM2⟩ := exists_nat_gt (1 / (ε^2/(16*((H:ℝ)^2*C^2+1))))
  have hex : ∀ d : ℕ, ∃ Nd : ℕ, ∀ M : ℕ, Nd ≤ M →
      (1 ≤ d → d < H →
        |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+d)) (x n)| < ε^2/16) := by
    intro d
    by_cases hd : 1 ≤ d ∧ d < H
    · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hcorr d hd.1) (ε^2/16) hK0pos
      refine ⟨N, fun M hM _ _ => ?_⟩
      have hdist := hN M hM
      rwa [dist_zero_right, Real.norm_eq_abs] at hdist
    · exact ⟨0, fun M _ h1 hH => absurd ⟨h1, hH⟩ hd⟩
  choose Nd hNd using hex
  refine ⟨max 1 (max NM1 (max NM2 ((Finset.range H).sup Nd))), fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMNM1 : NM1 ≤ M := by omega
  have hMNM2 : NM2 ≤ M := by omega
  have hMNcorr : (Finset.range H).sup Nd ≤ M := by omega
  have hMpos : (0:ℝ) < (M:ℝ) := Nat.cast_pos.mpr (by omega)
  have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
  have hM1nn : (0:ℝ) ≤ (M:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hMHnn : (0:ℝ) ≤ (M:ℝ)*(H:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hMHinv : (0:ℝ) ≤ ((M:ℝ)*(H:ℝ))⁻¹ := inv_nonneg.mpr hMHnn
  have hMinv01 : (M:ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
      _ = 1 * (M:ℝ) := by ring
  have hMinv1 : (M:ℝ)⁻¹ ≤ ε^2/(32*((H:ℝ)*C^2+1)) := by
    have h1 : (1:ℝ)/(ε^2/(32*((H:ℝ)*C^2+1))) < (M:ℝ) :=
      lt_of_lt_of_le hNM1 (Nat.cast_le.mpr hMNM1)
    have hδpos : (0:ℝ) < ε^2/(32*((H:ℝ)*C^2+1)) := div_pos hε2 (by positivity)
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) = (ε^2/(32*((H:ℝ)*C^2+1))) * (1/(ε^2/(32*((H:ℝ)*C^2+1)))) :=
          (mul_one_div_cancel (ne_of_gt hδpos)).symm
      _ ≤ (ε^2/(32*((H:ℝ)*C^2+1))) * (M:ℝ) :=
          mul_le_mul_of_nonneg_left h1.le hδpos.le
  have hMinv2 : (M:ℝ)⁻¹ ≤ ε^2/(16*((H:ℝ)^2*C^2+1)) := by
    have h1 : (1:ℝ)/(ε^2/(16*((H:ℝ)^2*C^2+1))) < (M:ℝ) :=
      lt_of_lt_of_le hNM2 (Nat.cast_le.mpr hMNM2)
    have hδpos : (0:ℝ) < ε^2/(16*((H:ℝ)^2*C^2+1)) := div_pos hε2 (by positivity)
    rw [inv_le_iff_one_le_mul₀ hMpos]
    calc (1:ℝ) = (ε^2/(16*((H:ℝ)^2*C^2+1))) * (1/(ε^2/(16*((H:ℝ)^2*C^2+1)))) :=
          (mul_one_div_cancel (ne_of_gt hδpos)).symm
      _ ≤ (ε^2/(16*((H:ℝ)^2*C^2+1))) * (M:ℝ) :=
          mul_le_mul_of_nonneg_left h1.le hδpos.le
  have hcsmall : ∀ d : ℕ, 1 ≤ d → d < H →
      |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+d)) (x n)| < ε^2/16 := by
    intro d hd1 hdH
    have hdmem : d ∈ Finset.range H := Finset.mem_range.mpr hdH
    have hle : Nd d ≤ M := le_trans (Finset.le_sup hdmem) hMNcorr
    exact hNd d M hle hd1 hdH
  have hN7i := sarkozy_vdc_avg_shift x C hC hx M H
  have hN7ii := sarkozy_vdc_sq_bound x M H
  -- off-diagonal correlation bound
  have hterm : ∀ h h' : ℕ, h ∈ Finset.range H → h' ∈ Finset.range H → h ≠ h' →
      |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
        ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
    intro h h' hh hh' hne
    have hhH : h < H := Finset.mem_range.mp hh
    have hh'H : h' < H := Finset.mem_range.mp hh'
    have hSTbound : ∀ S T : ℝ, ∀ e : ℝ,
        |S - T| ≤ e → |S| ≤ |T| + e := by
      intro S T e hST
      have hle := abs_sub_abs_le_abs_sub S T
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- h < h': swap slots, apply N7(iii) with big h'
      have hiii := sarkozy_vdc_corr_stable x C hC hx M h' h (le_of_lt hlt)
      have hd1 : 1 ≤ h' - h := by omega
      have hdH : h' - h < H := by omega
      have hsmall := hcsmall (h'-h) hd1 hdH
      have e : (∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
          = ∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h)) := by
        apply Finset.sum_congr rfl
        intro n _
        exact real_inner_comm _ _
      have hST := hSTbound _ _ _ hiii
      have hhHle : (h:ℝ) ≤ (H:ℝ) := by exact_mod_cast le_of_lt hhH
      have h2 : (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
        have hcc : 2*(h:ℝ)*C^2 ≤ 2*(H:ℝ)*C^2 := by
          calc 2*(h:ℝ)*C^2 = (2*C^2)*(h:ℝ) := by ring
            _ ≤ (2*C^2)*(H:ℝ) := mul_le_mul_of_nonneg_left hhHle (by positivity)
            _ = 2*(H:ℝ)*C^2 := by ring
        calc (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) = 2*(h:ℝ)*C^2*(M:ℝ)⁻¹ := by ring
          _ ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcc hM1nn
      calc |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
          = |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h))| := by
            rw [e]
        _ = (M:ℝ)⁻¹ * |(∑ n ∈ Finset.range M, inner ℝ (x (n+h')) (x (n+h)))| := by
            rw [abs_mul, abs_of_nonneg hM1nn]
        _ ≤ (M:ℝ)⁻¹ * (|(∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h'-h))) (x n))| + 2*(h:ℝ)*C^2) :=
            mul_le_mul_of_nonneg_left hST hM1nn
        _ = |(M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h'-h))) (x n))| + (M:ℝ)⁻¹*(2*(h:ℝ)*C^2) := by
            rw [abs_mul, abs_of_nonneg hM1nn]; ring
        _ ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ :=
            add_le_add (le_of_lt hsmall) h2
    · -- h' < h: direct from N7(iii)
      have hiii := sarkozy_vdc_corr_stable x C hC hx M h h' (le_of_lt hgt)
      have hd1 : 1 ≤ h - h' := by omega
      have hdH : h - h' < H := by omega
      have hsmall := hcsmall (h-h') hd1 hdH
      have hST := hSTbound _ _ _ hiii
      have hh'Hle : (h':ℝ) ≤ (H:ℝ) := by exact_mod_cast le_of_lt hh'H
      have h2 : (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by
        have hcc : 2*(h':ℝ)*C^2 ≤ 2*(H:ℝ)*C^2 := by
          calc 2*(h':ℝ)*C^2 = (2*C^2)*(h':ℝ) := by ring
            _ ≤ (2*C^2)*(H:ℝ) := mul_le_mul_of_nonneg_left hh'Hle (by positivity)
            _ = 2*(H:ℝ)*C^2 := by ring
        calc (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) = 2*(h':ℝ)*C^2*(M:ℝ)⁻¹ := by ring
          _ ≤ 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcc hM1nn
      calc |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))|
          = (M:ℝ)⁻¹ * |(∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))| := by
            rw [abs_mul, abs_of_nonneg hM1nn]
        _ ≤ (M:ℝ)⁻¹ * (|(∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h-h'))) (x n))| + 2*(h':ℝ)*C^2) :=
            mul_le_mul_of_nonneg_left hST hM1nn
        _ = |(M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ (x (n+(h-h'))) (x n))| + (M:ℝ)⁻¹*(2*(h':ℝ)*C^2) := by
            rw [abs_mul, abs_of_nonneg hM1nn]; ring
        _ ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ :=
            add_le_add (le_of_lt hsmall) h2
  -- diagonal bound
  have hdiag : ∀ h ∈ Finset.range H,
      (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h)) ≤ C^2 := by
    intro h _
    have hsq : ∀ n, inner ℝ (x (n+h)) (x (n+h)) = ‖x (n+h)‖^2 :=
      fun n => real_inner_self_eq_norm_sq _
    have hle : (∑ n ∈ Finset.range M, ‖x (n+h)‖^2) ≤ (M:ℝ) * C^2 := by
      calc (∑ n ∈ Finset.range M, ‖x (n+h)‖^2) ≤ ∑ _n ∈ Finset.range M, C^2 :=
            Finset.sum_le_sum (fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hx _) 2)
        _ = (M:ℝ) * C^2 := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h))
        = (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, ‖x (n+h)‖^2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          exact hsq n
      _ ≤ (M:ℝ)⁻¹ * ((M:ℝ) * C^2) := mul_le_mul_of_nonneg_left hle hM1nn
      _ = C^2 := by field_simp
  -- per-h inner sum bound
  have hKE : (0:ℝ) ≤ ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ := by positivity
  have hinner : ∀ h ∈ Finset.range H,
      (∑ h' ∈ Finset.range H, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ (x (n+h)) (x (n+h')))
        ≤ C^2 + (H:ℝ)*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    intro h hh
    have hsplit := (Finset.add_sum_erase (Finset.range H)
      (fun h' => (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))) hh).symm
    rw [hsplit]
    apply add_le_add (hdiag h hh)
    have hcards : (((Finset.range H).erase h).card : ℕ) ≤ H := by
      rw [Finset.card_erase_of_mem hh, Finset.card_range]
      exact Nat.sub_le _ _
    calc (∑ h' ∈ (Finset.range H).erase h, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ (x (n+h)) (x (n+h')))
        ≤ ∑ h' ∈ (Finset.range H).erase h,
            |(M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))| :=
          Finset.sum_le_sum (fun h' _ => le_abs_self _)
      _ ≤ ∑ _h' ∈ (Finset.range H).erase h, (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) :=
          Finset.sum_le_sum (fun h' h'mem => hterm h h' hh
            (Finset.mem_of_mem_erase h'mem)
            (Ne.symm (Finset.ne_of_mem_erase h'mem)))
      _ = (((Finset.range H).erase h).card : ℝ) * (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (H:ℝ) * (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ hKE
          exact_mod_cast hcards
  -- averaged total
  have hTdist : (M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
      = ∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ((M:ℝ)⁻¹ * ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h'))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
  have hTot : (M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))
      ≤ (H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    rw [hTdist]
    calc (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ (x (n+h)) (x (n+h')))
        ≤ ∑ h ∈ Finset.range H, (C^2 + (H:ℝ)*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) :=
          Finset.sum_le_sum (fun h hh => hinner h hh)
      _ = (H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- P and Q assembly
  have hS : (∑ n ∈ Finset.range M, x n)
      = ((H:ℝ))⁻¹ • ((H:ℝ) • ∑ n ∈ Finset.range M, x n) := by
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hHne, one_smul]
  have hAB : (M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
        - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
        = ((M:ℝ)*(H:ℝ))⁻¹ • ((H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)) := by
    rw [smul_sub]
    congr 1
    conv_lhs => rw [hS]
    rw [← smul_assoc, smul_eq_mul, ← mul_inv]
  have hQ : ((M:ℝ)*(H:ℝ))⁻¹ * ((H:ℝ)^2*C) = (H:ℝ)*C/(M:ℝ) := by
    field_simp
  have hAnorm : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
      ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
        + (H:ℝ)*C/(M:ℝ) := by
    have htri : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
        ≤ ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
          + ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
            - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖ := by
      calc ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)‖
            = ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))
              + ((M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
                - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)))‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have e1 : ‖((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
        = ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hMHnn]
    have e2 : ‖(M:ℝ)⁻¹ • (∑ n ∈ Finset.range M, x n)
          - ((M:ℝ)*(H:ℝ))⁻¹ • (∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h))‖
        = ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ := by
      rw [hAB, norm_smul, norm_inv, Real.norm_of_nonneg hMHnn]
    rw [e1, e2] at htri
    have h2 : ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
          - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖ ≤ (H:ℝ)*C/(M:ℝ) := by
      calc ((M:ℝ)*(H:ℝ))⁻¹ * ‖(H:ℝ) • (∑ n ∈ Finset.range M, x n)
            - ∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ((H:ℝ)^2*C) :=
            mul_le_mul_of_nonneg_left hN7i hMHinv
        _ = (H:ℝ)*C/(M:ℝ) := hQ
    linarith
  have hP2 : ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
        ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := by
    calc ((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        = ((((M:ℝ)*(H:ℝ))⁻¹)^2)
          * ((‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2) := by
          ring
      _ ≤ ((((M:ℝ)*(H:ℝ))⁻¹)^2)
          * ((M:ℝ) * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
            ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) :=
          mul_le_mul_of_nonneg_left hN7ii (pow_nonneg hMHinv 2)
      _ = ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
          ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := by
          field_simp
  have hPfin : ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
    calc ((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        ≤ ((H:ℝ))⁻¹^2 * ((M:ℝ)⁻¹ * (∑ h ∈ Finset.range H, ∑ h' ∈ Finset.range H,
            ∑ n ∈ Finset.range M, inner ℝ (x (n+h)) (x (n+h')))) := hP2
      _ ≤ ((H:ℝ))⁻¹^2 * ((H:ℝ)*C^2 + (H:ℝ)^2*(ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hTot (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 2)
      _ = C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹) := by
          field_simp
  -- numeric bounds for the 1/M terms
  have hfracbound : ∀ A : ℝ, 0 ≤ A → (ε^2/8)*(A/(A+1)) ≤ ε^2/8 := by
    intro A hA
    have hA1 : (0:ℝ) < A + 1 := by linarith
    have hle : A/(A+1) ≤ 1 := by
      rw [div_le_one hA1]
      linarith
    calc (ε^2/8)*(A/(A+1)) ≤ (ε^2/8)*1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ε^2/8 := by ring
  have h2E : 2*(2*(H:ℝ)*C^2*(M:ℝ)⁻¹) ≤ ε^2/8 := by
    have hEbound : 2*(H:ℝ)*C^2*(M:ℝ)⁻¹ ≤ 2*(H:ℝ)*C^2*(ε^2/(32*((H:ℝ)*C^2+1))) :=
      mul_le_mul_of_nonneg_left hMinv1 (by positivity)
    have hEeq : 2*(2*(H:ℝ)*C^2*(ε^2/(32*(((H:ℝ)*C^2)+1))))
        = (ε^2/8)*(((H:ℝ)*C^2)/(((H:ℝ)*C^2)+1)) := by
      have hA1 : ((H:ℝ)*C^2)+1 ≠ 0 := ne_of_gt (by positivity)
      have h1 : (32:ℝ)*(((H:ℝ)*C^2)+1) ≠ 0 := mul_ne_zero (by norm_num) hA1
      have h2 : (8:ℝ) ≠ 0 := by norm_num
      field_simp
      ring
    calc 2*(2*(H:ℝ)*C^2*(M:ℝ)⁻¹) ≤ 2*(2*(H:ℝ)*C^2*(ε^2/(32*(((H:ℝ)*C^2)+1)))) := by
            linarith [hEbound]
      _ = (ε^2/8)*(((H:ℝ)*C^2)/(((H:ℝ)*C^2)+1)) := hEeq
      _ ≤ ε^2/8 := hfracbound _ (by positivity)
  have hQ2 : ((H:ℝ)*C/(M:ℝ))^2 ≤ (H:ℝ)^2*C^2*(ε^2/(16*((H:ℝ)^2*C^2+1))) := by
    have hsq : ((H:ℝ)*C/(M:ℝ))^2 = (H:ℝ)^2*C^2*((M:ℝ)⁻¹*(M:ℝ)⁻¹) := by
      field_simp
    rw [hsq]
    have hnn : (0:ℝ) ≤ (H:ℝ)^2*C^2 := by positivity
    have hδ2nn : (0:ℝ) ≤ ε^2/(16*((H:ℝ)^2*C^2+1)) :=
      le_of_lt (div_pos hε2 (by positivity))
    have hmm : (M:ℝ)⁻¹*(M:ℝ)⁻¹ ≤ (ε^2/(16*((H:ℝ)^2*C^2+1)))*1 :=
      mul_le_mul hMinv2 hMinv01 hM1nn hδ2nn
    calc (H:ℝ)^2*C^2*((M:ℝ)⁻¹*(M:ℝ)⁻¹)
        ≤ (H:ℝ)^2*C^2*((ε^2/(16*((H:ℝ)^2*C^2+1)))*1) :=
          mul_le_mul_of_nonneg_left hmm hnn
      _ = (H:ℝ)^2*C^2*(ε^2/(16*((H:ℝ)^2*C^2+1))) := by ring
  have h2Q : 2*((H:ℝ)*C/(M:ℝ))^2 ≤ ε^2/8 := by
    have hQeq : 2*((H:ℝ)^2*C^2*(ε^2/(16*(((H:ℝ)^2*C^2)+1))))
        = (ε^2/8)*(((H:ℝ)^2*C^2)/(((H:ℝ)^2*C^2)+1)) := by
      have hA1 : ((H:ℝ)^2*C^2)+1 ≠ 0 := ne_of_gt (by positivity)
      have h1 : (16:ℝ)*(((H:ℝ)^2*C^2)+1) ≠ 0 := mul_ne_zero (by norm_num) hA1
      have h2 : (8:ℝ) ≠ 0 := by norm_num
      field_simp
      ring
    calc 2*((H:ℝ)*C/(M:ℝ))^2 ≤ 2*((H:ℝ)^2*C^2*(ε^2/(16*(((H:ℝ)^2*C^2)+1)))) := by
            linarith [hQ2]
      _ = (ε^2/8)*(((H:ℝ)^2*C^2)/(((H:ℝ)^2*C^2)+1)) := hQeq
      _ ≤ ε^2/8 := hfracbound _ (by positivity)
  -- final assembly with (a+b)^2 ≤ 2a^2 + 2b^2
  have hPl : 2*((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
      ≤ 2*(C^2/(H:ℝ) + (ε^2/16 + 2*(H:ℝ)*C^2*(M:ℝ)⁻¹)) := by
    have h := mul_le_mul_of_nonneg_left hPfin (show (0:ℝ) ≤ 2 by norm_num)
    linarith
  have hAsq : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2
      ≤ 2*((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
        + 2*(((H:ℝ)*C/(M:ℝ))^2) := by
    have hPQnn : (0:ℝ) ≤ ((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M,
          ∑ h ∈ Finset.range H, x (n + h)‖ + (H:ℝ)*C/(M:ℝ) := by positivity
    have h1 : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2
        ≤ (((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          + (H:ℝ)*C/(M:ℝ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hAnorm 2
    have h2 : ((((M:ℝ)*(H:ℝ))⁻¹ * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖
          + (H:ℝ)*C/(M:ℝ))^2)
        ≤ 2*((((M:ℝ)*(H:ℝ))⁻¹
          * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖)^2)
          + 2*(((H:ℝ)*C/(M:ℝ))^2) := by
      nlinarith [sq_nonneg ((((M:ℝ)*(H:ℝ))⁻¹
        * ‖∑ n ∈ Finset.range M, ∑ h ∈ Finset.range H, x (n + h)‖) - ((H:ℝ)*C/(M:ℝ)))]
    linarith
  have hfin : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2 ≤ ε^2/2 := by
    have h2C2H : 2*(C^2/(H:ℝ)) ≤ ε^2/8 := by linarith [hHC]
    have h2K0 : 2*(ε^2/16) = ε^2/8 := by ring
    linarith [hAsq, hPl, h2C2H, h2K0, h2E, h2Q]
  have hlt : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖^2 < ε^2 := by
    linarith [hfin, hε2]
  have hAlt : ‖(M:ℝ)⁻¹ • ∑ n ∈ Finset.range M, x n‖ < ε := by
    have h := abs_lt_of_sq_lt_sq hlt hε.le
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [dist_zero_right]
  exact hAlt

end MathlibExt.Combinatorics.Additive.SarkozyWanted
