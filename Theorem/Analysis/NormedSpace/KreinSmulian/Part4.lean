/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.List.GetD
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Def.Analysis.NormedSpace.KreinSmulian.Part4


namespace FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open scoped ComplexConjugate ZeroAtInfty

/-- Value of the indicator at its own point. -/
lemma ks_ind_self (p : ℕ × ℕ) : ks_ind p p = 1 := by
  change Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) p = 1
  exact Set.indicator_of_mem (Set.mem_singleton p) _

/-- Value of the indicator away from its point. -/
lemma ks_ind_other (p q : ℕ × ℕ) (h : q ≠ p) : ks_ind p q = 0 := by
  change Set.indicator ({p} : Set (ℕ × ℕ)) (fun _ => (1 : ℝ)) q = 0
  exact Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using h) _

/-- Sign times self is absolute value. -/
lemma ks_sign_mul_self (t : ℝ) : Real.sign t * t = |t| := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring

/-- Absolute value of a sign is at most one. -/
lemma ks_abs_sign (t : ℝ) : |Real.sign t| ≤ 1 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_neg, abs_one]
  · subst h; rw [Real.sign_zero, abs_zero]; exact zero_le_one
  · rw [Real.sign_of_pos h, abs_one]

/-- Empty.Finite sums in `C₀` evaluate pointwise. -/
lemma ks_sum_apply (S : Finset (ℕ × ℕ)) (g : (ℕ × ℕ) → C₀(ℕ × ℕ, ℝ)) (q : ℕ × ℕ) :
    (∑ p ∈ S, g p) q = ∑ p ∈ S, g p q := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  · intro a s has IH
    rw [Finset.sum_insert has, Finset.sum_insert has, ZeroAtInftyContinuousMap.add_apply,
      IH]

/-- Functionals on `C₀` give summable weights. -/
lemma ks_summable_weights (f : C₀(ℕ × ℕ, ℝ) →L[ℝ] ℝ) :
    Summable (fun p => f (ks_ind p)) := by
  apply Summable.of_abs
  refine summable_of_sum_le (c := ‖f‖) (fun _ => abs_nonneg _) ?_
  intro S
  set z : C₀(ℕ × ℕ, ℝ) := ∑ p ∈ S, (Real.sign (f (ks_ind p))) • ks_ind p with hz
  have hznorm : ‖z‖ ≤ 1 := by
    have hq : ∀ q : ℕ × ℕ, ‖z q‖ ≤ 1 := by
      intro q
      by_cases hqS : q ∈ S
      · have hzero : ∀ p ∈ S, p ≠ q → (Real.sign (f (ks_ind p)) • ks_ind p) q = 0 := by
          intro p hp hpq
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q (Ne.symm hpq),
            smul_zero]
        have e : z q = Real.sign (f (ks_ind q)) := by
          have e1 : z q = ∑ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q := by
            rw [hz, ks_sum_apply]
          rw [e1, Finset.sum_eq_single_of_mem q hqS hzero,
            ZeroAtInftyContinuousMap.smul_apply, ks_ind_self, smul_eq_mul, mul_one]
        rw [e, Real.norm_eq_abs]
        exact ks_abs_sign _
      · have hzero : ∀ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q = 0 := by
          intro p hp
          have hne : q ≠ p := by
            intro hcon
            subst hcon
            exact hqS hp
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q hne, smul_zero]
        have e : z q = 0 := by
          have e1 : z q = ∑ p ∈ S, ((Real.sign (f (ks_ind p))) • ks_ind p) q := by
            rw [hz, ks_sum_apply]
          rw [e1]
          exact Finset.sum_eq_zero hzero
        rw [e, norm_zero]
        exact zero_le_one
    have hBCF : ‖z.toBCF‖ ≤ 1 := by
      rw [BoundedContinuousFunction.norm_le zero_le_one]
      intro q
      exact hq q
    rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hBCF
  have hfz : f z = ∑ p ∈ S, |f (ks_ind p)| := by
    rw [hz, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, smul_eq_mul]
    exact ks_sign_mul_self _
  calc ∑ p ∈ S, |f (ks_ind p)| = f z := hfz.symm
    _ ≤ ‖f z‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    _ ≤ ‖f‖ * ‖z‖ := ContinuousLinearMap.le_opNorm f z
    _ ≤ ‖f‖ * 1 :=
      mul_le_mul_of_nonneg_left hznorm (ContinuousLinearMap.opNorm_nonneg f)
    _ = ‖f‖ := mul_one _

/-- Weights reconstruct the functional. -/
lemma ks_hasSum_weights (f : C₀(ℕ × ℕ, ℝ) →L[ℝ] ℝ) (y : C₀(ℕ × ℕ, ℝ)) :
    HasSum (fun p => f (ks_ind p) * y p) (f y) := by
  have hpart : ∀ S : Finset (ℕ × ℕ), ∑ p ∈ S, f (ks_ind p) * y p
      = f (∑ p ∈ S, (y p) • ks_ind p) := by
    intro S
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, smul_eq_mul, mul_comm]
  have hlim : Filter.Tendsto (fun S : Finset (ℕ × ℕ) => ∑ p ∈ S, (y p) • ks_ind p)
      Filter.atTop (nhds y) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hKfin : {p : ℕ × ℕ | ε / 2 ≤ ‖y p‖}.Finite := by
      have h0 : Filter.Tendsto (fun p : ℕ × ℕ => y p) Filter.cofinite (nhds (0 : ℝ)) := by
        have h0y := y.2
        rw [Filter.cocompact_eq_cofinite] at h0y
        exact h0y
      have hev : ∀ᶠ p : ℕ × ℕ in Filter.cofinite, dist (y p) 0 < ε / 2 :=
        h0.eventually (Metric.ball_mem_nhds 0 hε2)
      rw [Filter.eventually_cofinite] at hev
      apply Set.Finite.subset hev
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [dist_zero_right]
      exact not_lt.mpr hp
    obtain ⟨S₀, hS₀⟩ := Set.Finite.exists_finset hKfin
    rw [Filter.eventually_atTop]
    refine ⟨S₀, fun S hS => ?_⟩
    have hsub : S₀ ⊆ S := hS
    have hbound : ∀ q : ℕ × ℕ, ‖((∑ p ∈ S, (y p) • ks_ind p) - y) q‖ ≤ ε / 2 := by
      intro q
      by_cases hqS : q ∈ S
      · have hzero : ∀ p ∈ S, p ≠ q → ((y p) • ks_ind p) q = 0 := by
          intro p hp hpq
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q (Ne.symm hpq),
            smul_zero]
        have e : (∑ p ∈ S, (y p) • ks_ind p) q = y q := by
          have e1 : (∑ p ∈ S, (y p) • ks_ind p) q
              = ∑ p ∈ S, (((y p) • ks_ind p)) q := by
            rw [ks_sum_apply]
          rw [e1, Finset.sum_eq_single_of_mem q hqS hzero,
            ZeroAtInftyContinuousMap.smul_apply, ks_ind_self, smul_eq_mul, mul_one]
        rw [ZeroAtInftyContinuousMap.sub_apply, e, sub_self, norm_zero]
        exact le_of_lt hε2
      · have hzero : ∀ p ∈ S, (((y p) • ks_ind p)) q = 0 := by
          intro p hp
          have hne : q ≠ p := by
            intro hcon
            subst hcon
            exact hqS hp
          rw [ZeroAtInftyContinuousMap.smul_apply, ks_ind_other p q hne, smul_zero]
        have e : (∑ p ∈ S, (y p) • ks_ind p) q = 0 := by
          have e1 : (∑ p ∈ S, (y p) • ks_ind p) q
              = ∑ p ∈ S, (((y p) • ks_ind p)) q := by
            rw [ks_sum_apply]
          rw [e1]
          exact Finset.sum_eq_zero hzero
        have hqK : q ∉ ({p : ℕ × ℕ | ε / 2 ≤ ‖y p‖} : Set _) := by
          intro hmem
          rw [← hS₀] at hmem
          exact hqS (hsub hmem)
        have hlt : ‖y q‖ < ε / 2 := lt_of_not_ge (fun hle => hqK hle)
        rw [ZeroAtInftyContinuousMap.sub_apply, e, zero_sub, norm_neg]
        exact le_of_lt hlt
    have hnorm : ‖(∑ p ∈ S, (y p) • ks_ind p) - y‖ ≤ ε / 2 := by
      have hBCF : ‖((∑ p ∈ S, (y p) • ks_ind p) - y).toBCF‖ ≤ ε / 2 := by
        rw [BoundedContinuousFunction.norm_le hε2.le]
        intro q
        exact hbound q
      rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at hBCF
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hnorm (half_lt_self hε)
  have hlim2 : Filter.Tendsto (fun S : Finset (ℕ × ℕ) => ∑ p ∈ S, f (ks_ind p) * y p)
      Filter.atTop (nhds (f y)) := by
    have hcomp := (f.continuous.tendsto y).comp hlim
    simpa only [← hpart, Function.comp_def] using hcomp
  exact hlim2

/-- Separation: positive lower bound for real parts on `K`. -/
lemma ks_separation {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] {K : Set (WeakDual 𝕜 E)}
    (hKconv : Convex ℝ K) (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r)) :
    ∃ x : E, ∃ u : ℝ, 0 < u ∧ ∀ φ : WeakDual 𝕜 E, φ ∈ K → u ≤ RCLike.re (φ x) := by
  obtain ⟨δ, hδ, -, hgap⟩ := ks_norm_gap h0 (hK 1 zero_lt_one)
  have hKδ : K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) δ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro φ ⟨hφK, hφB⟩
    have hle : ‖WeakDual.toStrongDual φ‖ ≤ δ := mem_closedBall_zero_iff.mp hφB
    exact absurd hle (not_le.mpr (hgap φ hφK))
  obtain ⟨x, hx0, hxb, hxdet⟩ := ks_null_family hK hδ hKδ
  have himgconv : Convex ℝ ((ks_c0lin hx0) '' K) := by
    refine Convex.linear_image ?_ (ks_c0lin hx0)
    exact hKconv
  have hdisj : Disjoint (ball (0 : C₀(ℕ × ℕ, ℝ)) 1) ((ks_c0lin hx0) '' K) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨φ, hφK, hφg⟩
    have hlt : ‖g‖ < 1 := mem_ball_zero_iff.mp hg
    obtain ⟨p, hp⟩ := hxdet φ hφK
    have hpt := ks_c0norm hx0 φ p
    rw [hφg] at hpt
    have habs : RCLike.re (φ (x p)) ≤ |RCLike.re (φ (x p))| := le_abs_self _
    linarith
  obtain ⟨f, u, hfu_ball, hfu_K⟩ := geometric_hahn_banach_open
    (convex_ball (0 : C₀(ℕ × ℕ, ℝ)) 1) isOpen_ball himgconv hdisj
  have hu : 0 < u := by
    have h0mem : (0 : C₀(ℕ × ℕ, ℝ)) ∈ ball (0 : C₀(ℕ × ℕ, ℝ)) 1 := by simp
    have hlt := hfu_ball 0 h0mem
    simpa using hlt
  have hsum_abs : Summable (fun p : ℕ × ℕ => |f (ks_ind p)|) :=
    (ks_summable_weights f).abs
  have hsum_g : Summable (fun p : ℕ × ℕ => |f (ks_ind p)| * δ⁻¹) :=
    hsum_abs.mul_right _
  have hbound : ∀ p : ℕ × ℕ,
      ‖(↑(f (ks_ind p)) : 𝕜) • x p‖ ≤ |f (ks_ind p)| * δ⁻¹ := by
    intro p
    calc ‖(↑(f (ks_ind p)) : 𝕜) • x p‖ = |f (ks_ind p)| * ‖x p‖ := by
            rw [norm_smul, RCLike.norm_ofReal]
      _ ≤ |f (ks_ind p)| * δ⁻¹ :=
            mul_le_mul_of_nonneg_left (hxb p) (abs_nonneg _)
  have hsumm : Summable (fun p : ℕ × ℕ => (↑(f (ks_ind p)) : 𝕜) • x p) :=
    Summable.of_norm_bounded hsum_g hbound
  refine ⟨∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p, u, hu, fun φ hφ => ?_⟩
  have hge : u ≤ f (ks_c0lin hx0 φ) := hfu_K _ ⟨φ, hφ, rfl⟩
  have h1 : HasSum
      (fun p : ℕ × ℕ => (WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p))
      ((WeakDual.toStrongDual φ) (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p)) :=
    hsumm.hasSum.mapL (WeakDual.toStrongDual φ)
  have h2 : HasSum
      (fun p : ℕ × ℕ =>
        RCLike.re ((WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p)))
      (RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))) :=
    h1.mapL (RCLike.reCLM (K := 𝕜))
  have hterm : ∀ p : ℕ × ℕ, f (ks_ind p) * ks_c0lin hx0 φ p
      = RCLike.re ((WeakDual.toStrongDual φ) ((↑(f (ks_ind p)) : 𝕜) • x p)) := by
    intro p
    rw [map_smul, smul_eq_mul, RCLike.re_ofReal_mul, ks_c0lin_apply,
      WeakDual.toStrongDual_apply]
  have h3 : HasSum (fun p : ℕ × ℕ => f (ks_ind p) * ks_c0lin hx0 φ p)
      (RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))) :=
    h2.congr_fun (fun p => hterm p)
  have heq : RCLike.re ((WeakDual.toStrongDual φ)
        (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p)) = f (ks_c0lin hx0 φ) :=
    HasSum.unique h3 (ks_hasSum_weights f (ks_c0lin hx0 φ))
  have hφx : RCLike.re (φ (∑' p : ℕ × ℕ, (↑(f (ks_ind p)) : 𝕜) • x p))
      = f (ks_c0lin hx0 φ) := heq
  rw [hφx]
  exact hge

/-- `0` is not in the weak-* closure of `K`. -/
lemma ks_zero_notMem_closure {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {K : Set (WeakDual 𝕜 E)} (hKconv : Convex ℝ K) (h0 : (0 : WeakDual 𝕜 E) ∉ K)
    (hK : ∀ r : ℝ, 0 < r →
      IsClosed (K ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r)) :
    (0 : WeakDual 𝕜 E) ∉ closure K := by
  obtain ⟨x, u, hu, hbound⟩ := ks_separation hKconv h0 hK
  have hsub : K ⊆ {φ : WeakDual 𝕜 E | u ≤ RCLike.re (φ x)} :=
    fun φ hφ => hbound φ hφ
  have hcl : closure K ⊆ {φ : WeakDual 𝕜 E | u ≤ RCLike.re (φ x)} :=
    closure_minimal hsub (ks_isClosed_le_re x u)
  intro hmem
  have h0le : u ≤ RCLike.re ((0 : WeakDual 𝕜 E) x) := hcl hmem
  have h00 : ((0 : WeakDual 𝕜 E) x) = (0 : 𝕜) := by
    have h1 : WeakDual.toStrongDual (0 : WeakDual 𝕜 E) = 0 := map_zero _
    calc ((0 : WeakDual 𝕜 E) x) = (WeakDual.toStrongDual (0 : WeakDual 𝕜 E)) x :=
            (WeakDual.toStrongDual_apply _ _).symm
      _ = (0 : StrongDual 𝕜 E) x := by rw [h1]
      _ = 0 := by simp
  have h0r : RCLike.re (0 : 𝕜) = 0 := by simp
  rw [h00, h0r] at h0le
  linarith

/--
For a Banach space over `ℝ` or `ℂ` and `C ⊆ WeakDual 𝕜 E` convex over `ℝ`, `C` is weak-star closed
iff for every `r > 0` the intersection with each norm ball is weak-star closed. Source: M. Krein
and V. Smulian, Ann. of Math. 41 (1940) 556-583; Dunford-Schwartz I; Lean states `RCLike` Banach
case with `Convex ℝ s` and closedBall intersections.

Proves `Wanted` entry `krein_smulian`. -/
theorem krein_smulian
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {s : Set (WeakDual 𝕜 E)} (hs : Convex ℝ s) :
    IsClosed s ↔
      ∀ (r : ℝ) (_ : 0 < r),
        IsClosed
          (s ∩ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) := by
  constructor
  · intro hclosed r _hr
    exact hclosed.inter (ks_isClosed_ball r)
  · intro hball
    rw [← closure_subset_iff_isClosed]
    intro φ₀ hφ₀
    by_contra hφ₀out
    have h0K : (0 : WeakDual 𝕜 E) ∉ (fun ψ => ψ + φ₀) ⁻¹' s := by
      intro h
      simp only [Set.mem_preimage] at h
      rw [zero_add] at h
      exact hφ₀out h
    have hKconv : Convex ℝ ((fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s) := by
      intro a ha b hb α β hα hβ hαβ
      simp only [Set.mem_preimage] at ha hb ⊢
      have h := hs ha hb hα hβ hαβ
      rw [smul_add, smul_add, add_add_add_comm] at h
      rw [← Convex.combo_self hαβ φ₀]
      exact h
    have hKball : ∀ r : ℝ, 0 < r →
        IsClosed ((fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s ∩
          WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r) := by
      intro r hr
      have hrr : 0 < r + ‖WeakDual.toStrongDual φ₀‖ :=
        lt_of_lt_of_le hr (le_add_of_nonneg_right (norm_nonneg _))
      have hset : (fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹' s ∩
            WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r
          = (fun ψ : WeakDual 𝕜 E => ψ + φ₀) ⁻¹'
              (s ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E)
                (r + ‖WeakDual.toStrongDual φ₀‖))
            ∩ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r := by
        ext ψ
        simp only [Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨hψs, hψr⟩
          refine ⟨⟨hψs, ?_⟩, hψr⟩
          have hle : ‖WeakDual.toStrongDual ψ‖ ≤ r := mem_closedBall_zero_iff.mp hψr
          have hadd := norm_add_le (WeakDual.toStrongDual ψ) (WeakDual.toStrongDual φ₀)
          rw [← map_add] at hadd
          rw [mem_closedBall_zero_iff]
          linarith
        · rintro ⟨⟨hψs, -⟩, hψr⟩
          exact ⟨hψs, hψr⟩
      rw [hset]
      exact ((hball (r + ‖WeakDual.toStrongDual φ₀‖) hrr).preimage
        (continuous_id.add continuous_const)).inter (ks_isClosed_ball r)
    have h0cl : (0 : WeakDual 𝕜 E) ∈ closure ((fun ψ => ψ + φ₀) ⁻¹' s) := by
      have hmem : (Homeomorph.addRight φ₀) (0 : WeakDual 𝕜 E) ∈ closure s := by
        have h00 : (Homeomorph.addRight φ₀) (0 : WeakDual 𝕜 E) = φ₀ := by simp
        rw [h00]
        exact hφ₀
      have hpre : (0 : WeakDual 𝕜 E) ∈ (Homeomorph.addRight φ₀) ⁻¹' closure s := hmem
      rw [(Homeomorph.addRight φ₀).preimage_closure] at hpre
      have hKK : (Homeomorph.addRight φ₀) ⁻¹' s = (fun ψ => ψ + φ₀) ⁻¹' s := by
        rw [Homeomorph.coe_addRight]
      rw [hKK] at hpre
      exact hpre
    exact (ks_zero_notMem_closure hKconv h0K hKball) h0cl

end FunctionalAnalysis.BanachSpaceWanted
