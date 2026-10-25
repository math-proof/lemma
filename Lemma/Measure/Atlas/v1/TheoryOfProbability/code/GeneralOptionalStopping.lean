import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfProbability.code.GeneralOptionalStopping
open MeasureTheory Filter


/--
[coe_untopA_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean)
-/
@[path]
lemma coe_untopA_eq
  {a : ℕ∞}
-- given
  (ha : a ≠ ⊤) :
-- imply
  (↑(a.untopA) : ℕ∞) = a := by
-- proof
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha
  rw [← hn]
  simp only [WithTop.untopA, WithTop.untopD, WithTop.recTopCoe]
  rfl

/--
[general_optional_stopping_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/GeneralOptionalStopping.lean)
-/
@[path]
lemma general_optional_stopping_bounded
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {ℱ : Filtration ℕ m0}
  [SigmaFiniteFiltration μ ℱ]
  {f : ℕ → Ω → ℝ}
  {L M : Ω → ℕ∞}
  {N : ℕ}
  [SigmaFinite (μ.trim hL.measurableSpace_le)]
-- given
  (hsub : Submartingale f ℱ μ)
  (hL : IsStoppingTime ℱ L)
  (hM : IsStoppingTime ℱ M)
  (hLM : L ≤ M)
  (hbdd : ∀ ω, M ω ≤ N) :
-- imply
  (∫ ω, stoppedValue f L ω ∂μ ≤ ∫ ω, stoppedValue f M ω ∂μ) ∧ (stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace]) := by
-- proof
  constructor
  · exact hsub.expected_stoppedValue_mono hL hM hLM hbdd
  · have h_sp_sub : Submartingale (stoppedProcess f M) ℱ μ := hsub.stoppedProcess hM
    have hL_bdd : ∀ ω, L ω ≤ N := fun ω => (hLM ω).trans (hbdd ω)
    have hL_ne_top : ∀ ω, L ω ≠ ⊤ := fun ω =>
      ne_top_of_le_ne_top (ne_top_of_le_ne_top (by simp) (hbdd ω)) (hLM ω)
    have h_sp_N : stoppedProcess f M N = stoppedValue f M := by
      funext ω
      exact stoppedProcess_eq_of_ge (hbdd ω)
    have h_key : ∀ᵐ ω ∂μ, ∀ k : ℕ, L ω = ↑k →
      stoppedProcess f M k ω ≤
        (μ[stoppedValue f M | hL.measurableSpace]) ω := by
      rw [ae_all_iff]
      intro k
      by_cases hkN : k ≤ N
      · have h_ineq_k : stoppedProcess f M k ≤ᵐ[μ] μ[stoppedValue f M | ℱ k] := by
        have := h_sp_sub.ae_le_condExp hkN
        rwa [h_sp_N] at this
        have h_ce_restrict :
          μ[stoppedValue f M | hL.measurableSpace]
            =ᵐ[μ.restrict {ω | L ω = ↑k}]
            μ[stoppedValue f M | ℱ k] :=
          condExp_ae_eq_restrict_of_measurableSpace_eq_on
            hL.measurableSpace_le (ℱ.le k) (hL.measurableSet_eq' k)
            (fun t => by rw [Set.inter_comm]; exact hL.measurableSet_inter_eq_iff t k)
        have h_restrict := (ae_restrict_iff'
          (ℱ.le _ _ (hL.measurableSet_eq k))).mp h_ce_restrict
        filter_upwards [h_restrict, h_ineq_k] with ω hω_ce hω_ineq hLk
        calc stoppedProcess f M k ω
          ≤ (μ[stoppedValue f M | ℱ k]) ω := hω_ineq
          _ = (μ[stoppedValue f M | hL.measurableSpace]) ω := (hω_ce hLk).symm
      · have hNk : N < k := Nat.lt_of_not_le hkN
        filter_upwards with ω hLk
        exfalso
        have : L ω ≤ ↑N := hL_bdd ω
        rw [hLk] at this
        exact Nat.not_lt.mpr (mod_cast this) hNk
    filter_upwards [h_key] with ω hω
    have h_sv_eq : stoppedValue f L ω = stoppedProcess f M (L ω).untopA ω := by
      simp only [stoppedValue]
      rw [stoppedProcess_eq_of_le ((coe_untopA_eq _ (hL_ne_top ω)).le.trans (hLM ω))]
    rw [h_sv_eq]
    exact hω _ (coe_untopA_eq _ (hL_ne_top ω)).symm
/-- **General optional stopping theorem (expectation inequality form)**. Let `f` be
a uniformly integrable submartingale and `τ : Ω → ℕ∞` any stopping time (possibly
infinite). Then `E[f_0] ≤ E[f_τ] ≤ E[f_∞]`, where `f_∞ = lim_{n → ∞} f n` and
`f_τ` is given by `stoppedValueExtended`. This corresponds to the textbook statement
"Let `X_n` be a uniformly integrable submartingale; for any stopping time `N ≤ ∞` we
have `EX_0 ≤ EX_N ≤ EX_∞`." -/


-- created on 2026-10-23
