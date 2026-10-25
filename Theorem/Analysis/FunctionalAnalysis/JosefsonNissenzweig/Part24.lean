/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Lemma.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part25


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

@[simp] theorem jn_l1Extension_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m i : ℕ) :
    jnL1Extension hc hx m (x i) = jnRademacher i m := by
  rw [show jnL1Extension hc hx m (x i) =
      jnL1SignFunctional hc hx m
        ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ by
    let y : Submodule.span ℝ (Set.range x) :=
      ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
    change Classical.choose (exists_extension_norm_eq
      (Submodule.span ℝ (Set.range x)) (jnL1SignFunctional hc hx m)) (y : E) =
        jnL1SignFunctional hc hx m y
    exact (Classical.choose_spec (exists_extension_norm_eq
      (Submodule.span ℝ (Set.range x)) (jnL1SignFunctional hc hx m))).1 y]
  exact jn_l1SignFunctional_apply hc hx m i

theorem jn_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℝ E) :
    ∃ (ψ : ℕ → StrongDual ℝ E), (∀ n, ‖ψ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨R, z, hR, hzbound, hzsep⟩ := jn_exists_separated_dual_sequence hInf
  have hbounded : Bornology.IsBounded (Set.range z) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * R, fun m n => ?_⟩
    rw [dist_eq_norm]
    calc
      ‖z m - z n‖ ≤ ‖z m‖ + ‖z n‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hzbound m) (hzbound n)
      _ = 2 * R := by ring
  obtain ⟨u, hu, hweak | hlower⟩ :=
    MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted.rosenthal_l1
      (𝕜 := ℝ) (E := StrongDual ℝ E) z hbounded
  · apply jn_of_pointwise_cauchy_subsequence z hzsep u hu
    intro x
    apply Metric.cauchySeq_iff.2
    intro ε hε
    let f : StrongDual ℝ E →L[ℝ] ℝ :=
      NormedSpace.inclusionInDoubleDual ℝ E x
    obtain ⟨N, hN⟩ := hweak f ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [f, NormedSpace.dual_def, dist_eq_norm] using hN m n hm hn
  · obtain ⟨c, hc, hclower⟩ := jn_l1Lower_of_uniform hlower
    let y : ℕ → StrongDual ℝ E := z ∘ u
    have hybound : ∀ n, ‖y n‖ ≤ R := fun n => hzbound (u n)
    rcases jn_stable_block_or_pointwise_null y with hnull | hstable
    · obtain ⟨b, hbnull⟩ := hnull
      let w : ℕ → StrongDual ℝ E := jnBlockApply b y
      have hwlower : ∀ n, c ≤ ‖w n‖ :=
        jn_l1Lower_norm (jn_block_preserves_l1_lower hclower b)
      exact jn_of_lower_bounded_pointwise_null w c hc hwlower hbnull
    · obtain ⟨b, δ, hδ, hbstable⟩ := hstable
      let w : ℕ → StrongDual ℝ E := jnBlockApply b y
      have hwbound : ∀ n, ‖w n‖ ≤ R := jn_block_preserves_bound hybound b
      exact jn_of_stable_block hδ w hwbound hbstable

/--
If `E` is an infinite-dimensional Banach space over `𝕜 = ℝ` or `ℂ`, then its strong dual contains
a sequence of norm-one functionals that converges weak-star to zero, i.e. `‖φ n‖ = 1` for all `n`
and `(φ n) x → 0` for every `x : E`. Source: B. Josefson, Weak sequential convergence in the
dual of a Banach space does not imply norm convergence, Bull. Amer. Math. Soc. 81 (1975),
166–168, DOI 10.1090/S0002-9904-1975-13691-3; and A. Nissenzweig, w* sequential convergence,
Israel J. Math. 22 (1975), 266–272, DOI 10.1007/BF02761594, Josefson-Nissenzweig theorem;
Diestel, Sequences and Series; Lean states `RCLike` infinite-dimensional Banach case with
`‖φ n‖=1` and pointwise weak-star nullness.

Proves `Wanted` entry `josefson_nissenzweig`.

Proof: We apply Rosenthal's `ℓ¹` dichotomy to a separated dual sequence, then use the stable-block
and Banach-limit/Rademacher route of Hagler--Johnson (1977) and Behrends (1995).
-/
theorem josefson_nissenzweig
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  exact jn_rclike_of_real hInf jn_real

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
