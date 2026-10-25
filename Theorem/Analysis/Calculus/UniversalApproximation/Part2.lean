import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Analysis.Calculus.UniversalApproximation.Part2
open scoped BigOperators Pointwise

/-!
# Universal approximation theorem

Proves `Wanted` entry `universal_approximation`.
-/


namespace MetaMathlibExt.UniversalApprox

theorem mollify_smooth (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mollify φ σ) :=
  HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContDiffBump.hasCompactSupport_normed φ) (ContDiffBump.contDiff_normed φ)
    hσ.locallyIntegrable

theorem mollify_eq_integral (σ : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ))
    (t : ℝ) :
    mollify φ σ t
      = ∫ s in (-φ.rOut)..φ.rOut,
        (φ.normed MeasureTheory.volume) s * σ (t - s) := by
  set ψ : ℝ → ℝ := φ.normed MeasureTheory.volume with hψ
  set r : ℝ := φ.rOut with hr
  have hrpos : 0 < r := φ.rOut_pos
  have hle : -r ≤ r := by linarith
  have hsupp : ∀ s ∉ Metric.ball (0 : ℝ) r, ψ s = 0 := by
    intro s hs
    have hmem : s ∉ Function.support ψ := by
      rw [hψ, ContDiffBump.support_normed_eq, ← hr]
      exact hs
    by_contra hne
    exact hmem (Function.mem_support.mpr hne)
  have hconv : mollify φ σ t = ∫ s, ψ s * σ (t - s) := by
    simp only [mollify, hψ, MeasureTheory.convolution_lsmul, smul_eq_mul]
  have hIoc : (∫ s, ψ s * σ (t - s))
      = ∫ s in Set.Ioc (-r) r, ψ s * σ (t - s) := by
    apply (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro s hs
    have hbeq : Metric.ball (0 : ℝ) r = Set.Ioo (-r) r := by
      rw [Real.ball_eq_Ioo]
      simp only [zero_sub, zero_add]
    have hball : s ∉ Metric.ball (0 : ℝ) r := by
      rw [hbeq]
      exact fun hmem => hs (Set.Ioo_subset_Ioc_self hmem)
    rw [hsupp s hball, zero_mul]
  rw [hconv, intervalIntegral.integral_of_le hle]
  exact hIoc

theorem mollify_sigmaApprox (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ContDiffBump (0 : ℝ)) : sigmaApprox σ (mollify φ σ) := by
  set ψ : ℝ → ℝ := φ.normed MeasureTheory.volume with hψ
  set r : ℝ := φ.rOut with hr
  have hrpos : 0 < r := φ.rOut_pos
  have hab : -r ≤ r := by linarith
  have hψcont : Continuous ψ := ContDiffBump.continuous_normed φ
  have hF : Continuous
      (Function.uncurry (fun t s => ψ s * σ (t - s))) :=
    (hψcont.comp continuous_snd).mul (hσ.comp (continuous_fst.sub continuous_snd))
  intro R ε hε
  obtain ⟨N, hNpos, herr⟩ :=
    riemann_sum_uniform (fun t s => ψ s * σ (t - s)) hF hab R hε
  set h : ℝ := (r - -r) / N with hh
  have hgint : ∀ t, mollify φ σ t = ∫ s in (-r)..r, ψ s * σ (t - s) :=
    fun t => mollify_eq_integral σ φ t
  refine ⟨N, fun j => h * ψ (-r + (j : ℝ) * h), fun _ => 1,
    fun j => -(-r + (j : ℝ) * h), fun t ht => ?_⟩
  have e := herr t ht
  have hsum_eq :
      (∑ i : Fin N, (h * ψ (-r + (i : ℝ) * h))
          * σ (1 * t + -(-r + (i : ℝ) * h)))
        = ∑ j ∈ Finset.range N,
          h * (ψ (-r + (j : ℝ) * h) * σ (t - (-r + (j : ℝ) * h))) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have h1t : 1 * t + -(-r + (i : ℝ) * h) = t - (-r + (i : ℝ) * h) := by ring
    rw [h1t]
    ring
  have e2 : |mollify φ σ t
      - ∑ j ∈ Finset.range N,
        h * (ψ (-r + (j : ℝ) * h) * σ (t - (-r + (j : ℝ) * h)))| < ε := by
    rw [hgint t]
    exact e
  change |mollify φ σ t
    - ∑ i : Fin N, (h * ψ (-r + (i : ℝ) * h))
      * σ (1 * t + -(-r + (i : ℝ) * h))| < ε
  rw [hsum_eq]
  exact e2

theorem mollify_tendsto (σ : ℝ → ℝ) (hσ : Continuous σ)
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Filter.Tendsto (fun j => (φ j).rOut) Filter.atTop (nhds 0)) (x : ℝ) :
    Filter.Tendsto (fun j => mollify (φ j) σ x) Filter.atTop (nhds (σ x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous hφ hσ x

theorem eq_polynomial_of_iteratedDeriv_eq_zero (g : ℝ → ℝ)
    (hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (k : ℕ)
    (hder : ∀ x, iteratedDeriv k g x = 0) :
    ∃ p : Polynomial ℝ, p.degree < (k : WithBot ℕ) ∧ ∀ x, g x = p.eval x := by
  rcases k with _ | n
  · have hdeg0 : (0 : Polynomial ℝ).degree < ((0 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe 0
    refine ⟨0, hdeg0, fun x => ?_⟩
    have h := hder x
    rw [iteratedDeriv_zero] at h
    simp only [h, Polynomial.eval_zero]
  · set f : Fin (n + 1) → ℝ :=
      fun i => iteratedDeriv (i : ℕ) g 0 / (((i : ℕ).factorial : ℕ) : ℝ) with hf
    set p : Polynomial ℝ :=
      ∑ i, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ) with hp
    have hdeg : p.degree < ((n + 1 : ℕ) : WithBot ℕ) :=
      Polynomial.degree_sum_fin_lt f
    have hpeval : ∀ x, p.eval x = ∑ i : Fin (n + 1), f i * x ^ (i : ℕ) := by
      intro x
      simp only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    refine ⟨p, hdeg, fun x => ?_⟩
    by_cases hx0 : x = 0
    · subst hx0
      have hrest :
          (∑ i : Fin n, f i.succ * (0 : ℝ) ^ ((i.succ : Fin (n + 1)) : ℕ))
          = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hexp : ((i.succ : Fin (n + 1)) : ℕ) ≠ 0 := by
          have hvs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
          omega
        rw [zero_pow hexp, mul_zero]
      have hf0 : f 0 = g 0 := by
        simp only [hf]
        have hv0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
        rw [hv0, iteratedDeriv_zero]
        rw [Nat.factorial_zero, Nat.cast_one, div_one]
      rw [hpeval, Fin.sum_univ_succ, hrest, add_zero]
      have hv0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
      rw [hv0, pow_zero, mul_one]
      exact hf0.symm
    · have hle : ((n : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [← hcast]
        exact natCast_le_top_smooth (n + 1)
      have hco : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) g (Set.uIcc 0 x) :=
        (hgs.of_le hle).contDiffOn
      obtain ⟨x', hx', hrem⟩ :=
        taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := x) (n := n)
          (Ne.symm hx0) hco
      have hvan : iteratedDeriv (n + 1) g x' = 0 := hder x'
      rw [hvan, zero_mul, zero_div] at hrem
      have hgx : g x = taylorWithinEval g n (Set.uIcc 0 x) 0 x :=
        sub_eq_zero.mp hrem
      have huniq : UniqueDiffOn ℝ (Set.uIcc 0 x) := by
        rcases lt_or_gt_of_ne hx0 with hneg | hpos
        · rw [Set.uIcc_of_ge (le_of_lt hneg)]
          exact uniqueDiffOn_Icc hneg
        · rw [Set.uIcc_of_le (le_of_lt hpos)]
          exact uniqueDiffOn_Icc hpos
      have htaylor : taylorWithinEval g n (Set.uIcc 0 x) 0 x = p.eval x := by
        rw [taylor_within_apply, hpeval x, Finset.sum_range]
        apply Finset.sum_congr rfl
        intro i _
        have hAt : ContDiffAt ℝ ((i : ℕ) : WithTop ℕ∞) g 0 :=
          (hgs.of_le (natCast_le_top_smooth (i : ℕ))).contDiffAt
        have hiW : iteratedDerivWithin (i : ℕ) g (Set.uIcc 0 x) 0
            = iteratedDeriv (i : ℕ) g 0 :=
          iteratedDerivWithin_eq_iteratedDeriv huniq hAt Set.left_mem_uIcc
        rw [hiW]
        simp only [hf]
        rw [sub_zero, smul_eq_mul, div_eq_mul_inv]
        ring
      rw [hgx, htaylor]

theorem sigmaApprox_monomial (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x) (k : ℕ) :
    sigmaApprox σ (fun t ↦ t ^ k) := by
  set φ : ℕ → ContDiffBump (0 : ℝ) := fun j =>
    ⟨1 / ((j : ℝ) + 2), 1 / ((j : ℝ) + 1), by positivity, by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (j : ℝ) + 1 < (j : ℝ) + 2 := by linarith
      exact one_div_lt_one_div_of_lt h1 h2⟩ with hφ
  have hrOut : Filter.Tendsto (fun j => (φ j).rOut) Filter.atTop (nhds 0) := by
    simp only [hφ]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases hcase : ∃ j b, iteratedDeriv k (mollify (φ j) σ) b ≠ 0
  · obtain ⟨j, b, hne⟩ := hcase
    have hg := mollify_sigmaApprox σ hσ (φ j)
    have hgs := mollify_smooth σ hσ (φ j)
    have hmain : sigmaApprox σ
        (fun t ↦ t ^ k * iteratedDeriv k (mollify (φ j) σ) (0 * t + b)) :=
      sigmaApprox_weight_derivative σ (mollify (φ j) σ) hg hgs k 0 b
    set c : ℝ := iteratedDeriv k (mollify (φ j) σ) b with hc
    have hfun : (fun t ↦ t ^ k * iteratedDeriv k (mollify (φ j) σ) (0 * t + b))
        = (fun t ↦ t ^ k * c) := by
      funext t
      rw [zero_mul, zero_add, hc]
    rw [hfun] at hmain
    have hcne : c ≠ 0 := hne
    have hmono := sigmaApprox_const_mul σ (fun t ↦ t ^ k * c) c⁻¹ hmain
    have hfun2 : (fun t ↦ c⁻¹ * (t ^ k * c)) = (fun t ↦ t ^ k) := by
      funext t
      calc c⁻¹ * (t ^ k * c) = (c⁻¹ * c) * t ^ k := by ring
        _ = 1 * t ^ k := by rw [inv_mul_cancel₀ hcne]
        _ = t ^ k := one_mul _
    rw [hfun2] at hmono
    exact hmono
  · push Not at hcase
    have hP : ∀ j, ∃ P : Polynomial ℝ,
        P.degree < (k : WithBot ℕ) ∧ ∀ x, mollify (φ j) σ x = P.eval x := by
      intro j
      exact eq_polynomial_of_iteratedDeriv_eq_zero (mollify (φ j) σ)
        (mollify_smooth σ hσ (φ j)) k (hcase j)
    choose P hPdeg hPeq using hP
    have hlim : ∀ x, Filter.Tendsto (fun j => (P j).eval x) Filter.atTop
        (nhds (σ x)) := by
      intro x
      have hconv := mollify_tendsto σ hσ φ hrOut x
      have heq : (fun j => (P j).eval x) = (fun j => mollify (φ j) σ x) := by
        funext j
        exact (hPeq j x).symm
      rw [heq]
      exact hconv
    obtain ⟨p, hp⟩ := polynomial_of_tendsto_degreeLT k P σ hPdeg hlim
    exact absurd ⟨p, hp⟩ hnp

theorem sigmaApprox_polynomial (σ : ℝ → ℝ)
    (hmon : ∀ k : ℕ, sigmaApprox σ (fun t ↦ t ^ k)) (p : Polynomial ℝ) :
    sigmaApprox σ (fun t ↦ p.eval t) := by
  have heq : (fun t ↦ p.eval t)
      = (fun t ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * t ^ i) := by
    funext t
    exact Polynomial.eval_eq_sum_range t
  rw [heq]
  refine sigmaApprox_sum σ (Finset.range (p.natDegree + 1))
    (fun i t => p.coeff i * t ^ i) ?_
  intro i _
  exact sigmaApprox_const_mul σ _ _ (hmon i)

theorem sigmaApprox_of_continuous (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x) (g : ℝ → ℝ)
    (hg : Continuous g) : sigmaApprox σ g := by
  apply sigmaApprox_of_near σ _ (fun R ε hε => ?_)
  have hcont : ContinuousOn g (Set.Icc (-R) R) := hg.continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R g hcont ε hε
  refine ⟨fun t => p.eval t,
    sigmaApprox_polynomial σ (sigmaApprox_monomial σ hσ hnp) p, fun t ht => ?_⟩
  have hmem : t ∈ Set.Icc (-R) R := abs_le.mp ht
  have h := hp t hmem
  rw [abs_sub_comm]
  exact h

theorem netApproxOn_sum {ι : Type*} (σ : ℝ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) (s : Finset ι)
    (g : ι → E → ℝ) (hg : ∀ i ∈ s, netApproxOn σ K (g i)) :
    netApproxOn σ K (fun x ↦ ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun x => ∑ i ∈ (∅ : Finset ι), g i x) = 0 := by funext x; simp
    rw [this]
    exact netApproxOn_zero σ K
  | insert a s ha ih =>
    have ha' : ∀ i ∈ s, netApproxOn σ K (g i) :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hga : netApproxOn σ K (g a) := hg a (Finset.mem_insert_self a s)
    have ih' := ih ha'
    have hadd := netApproxOn_add σ hga ih'
    have heq : (fun x => ∑ i ∈ insert a s, g i x)
        = ((g a) + (fun x => ∑ i ∈ s, g i x)) := by
      funext x
      simp [Finset.sum_insert ha, Pi.add_apply]
    rw [heq]
    exact hadd

theorem exists_expSum_near {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Set E} (hK : IsCompact K) {f : E → ℝ}
    (hf : ContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℝ) (v : Fin m → E),
      ∀ x ∈ K, |f x - ∑ j, a j * Real.exp (inner ℝ (v j) x)| < ε := by
  set e : E → C(K, ℝ) := fun v =>
    { toFun := fun x => Real.exp (inner ℝ v (x : E)),
      continuous_toFun := Real.continuous_exp.comp
        (continuous_const.inner continuous_subtype_val) } with he
  set S : Submodule ℝ C(K, ℝ) := Submodule.span ℝ (Set.range e) with hS
  have h1 : (1 : C(K, ℝ)) ∈ S := by
    have he0 : e 0 = 1 := by
      apply ContinuousMap.ext
      intro x
      simp only [he, ContinuousMap.coe_mk, inner_zero_left, Real.exp_zero,
        ContinuousMap.one_apply]
    rw [← he0]
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hsub : Set.range e * Set.range e ⊆ Set.range e := by
    rw [Set.mul_subset_iff]
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    have hadd : e a * e b = e (a + b) := by
      apply ContinuousMap.ext
      intro x
      simp only [he, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
        inner_add_left, Real.exp_add]
    rw [hadd]
    exact Set.mem_range_self (a + b)
  have hmul : ∀ x y : C(K, ℝ), x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hmem : x * y ∈ S * S := Submodule.mul_mem_mul hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      exact Submodule.span_mono hsub
    exact hle hmem
  set A : Subalgebra ℝ C(K, ℝ) := S.toSubalgebra h1 hmul with hA
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    set v : E := (x : E) - (y : E) with hv
    have hxyE : (x : E) ≠ (y : E) := fun h => hxy (Subtype.ext h)
    have hne : (x : E) - (y : E) ≠ 0 := sub_ne_zero.mpr hxyE
    have hnorm : ‖(x : E) - (y : E)‖ ≠ 0 := fun h => hne (norm_eq_zero.mp h)
    have hpos : (0 : ℝ) < ‖(x : E) - (y : E)‖ ^ 2 := by positivity
    have hdiff : inner ℝ v (x : E) - inner ℝ v (y : E)
        = ‖(x : E) - (y : E)‖ ^ 2 := by
      have h1 : inner ℝ v (x : E) - inner ℝ v (y : E) = inner ℝ v v := by
        rw [hv, inner_sub_right]
      rw [h1]
      exact real_inner_self_eq_norm_sq v
    have hinner : inner ℝ v (x : E) ≠ inner ℝ v (y : E) := by
      intro heq
      rw [heq, sub_self] at hdiff
      linarith
    have hexp : Real.exp (inner ℝ v (x : E))
        ≠ Real.exp (inner ℝ v (y : E)) := fun h => hinner (Real.exp_injective h)
    have hmemS : e v ∈ S := Submodule.subset_span (Set.mem_range_self v)
    have hmemA : e v ∈ (A : Set C(K, ℝ)) := hmemS
    refine ⟨_, Set.mem_image_of_mem _ hmemA, ?_⟩
    simp only [he, ContinuousMap.coe_mk]
    exact hexp
  have hfcont : Continuous (K.domRestrict f) := hf.domRestrict
  obtain ⟨g, hg⟩ :=
    @ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _ _
      (isCompact_iff_compactSpace.mp hK) A hsep (K.domRestrict f) hfcont ε hε
  have hgS : (g : C(K, ℝ)) ∈ S := g.property
  rw [hS, Submodule.mem_span_set'] at hgS
  obtain ⟨m, a, v, hsum⟩ := hgS
  have hw : ∀ i, ∃ w : E, e w = (v i : C(K, ℝ)) := by
    intro i
    obtain ⟨w, hww⟩ := (v i).property
    exact ⟨w, hww⟩
  choose w hw using hw
  refine ⟨m, a, w, fun x hx => ?_⟩
  have hpt := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at hpt
  have hcoe : (((∑ i, a i • ((v i : C(K, ℝ)))) : C(K, ℝ)) : K → ℝ)
      = ∑ i, (((a i • ((v i : C(K, ℝ)))) : C(K, ℝ)) : K → ℝ) :=
    map_sum ContinuousMap.coeFnAddMonoidHom _ _
  have happly := congrArg (fun F : K → ℝ => F ⟨x, hx⟩) hcoe
  simp only [Finset.sum_apply] at happly
  have hval : (g : C(K, ℝ)) ⟨x, hx⟩
      = ∑ j, a j * Real.exp (inner ℝ (w j) x) := by
    calc (g : C(K, ℝ)) ⟨x, hx⟩
        = (∑ i, a i • ((v i : C(K, ℝ)))) ⟨x, hx⟩ := by rw [hsum]
      _ = ∑ i, (a i • ((v i : C(K, ℝ)))) ⟨x, hx⟩ := happly
      _ = ∑ j, a j * Real.exp (inner ℝ (w j) x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ContinuousMap.smul_apply, smul_eq_mul]
          congr 1
          rw [← hw i]
          simp only [he, ContinuousMap.coe_mk]
  rw [hval] at hpt
  have hdom : K.domRestrict f ⟨x, hx⟩ = f x := rfl
  rw [hdom, abs_sub_comm] at hpt
  exact hpt

end MetaMathlibExt.UniversalApprox

namespace MetaMathlibExt

/-- Universal approximation theorem (`universal-approximation-s1` from
https://en.wikipedia.org/wiki/Universal_approximation_theorem): a single-hidden-layer
feedforward network with activation `σ` maps `x` to
`∑ i, c i * σ (@inner ℝ _ _ (W i) x + b i)`; if `σ` is continuous and non-polynomial,
such networks are dense in `C(K)` under the uniform norm on every compact `K`.
This is the continuous-activation case of the theorem of M. Leshno, V. Ya. Lin, A. Pinkus and
S. Schocken, *Multilayer feedforward networks with a nonpolynomial activation function can
approximate any function*, Neural Networks 6(6) (1993), 861–867,
doi:10.1016/S0893-6080(05)80131-5, which allows any locally bounded, piecewise continuous
activation that is not almost everywhere equal to a polynomial; for continuous `σ` this is the
same as the pointwise hypothesis `_hnp`.

Proves `Wanted` entry `universal_approximation`.
-/
theorem universal_approximation :
    ∀ {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (_hK : IsCompact K)
      {σ : ℝ → ℝ} (_hσ : Continuous σ)
      (_hnp : ¬ ∃ p : Polynomial ℝ, ∀ x, σ x = p.eval x)
      {f : EuclideanSpace ℝ (Fin n) → ℝ} (_hf : ContinuousOn f K)
      {ε : ℝ} (_hε : 0 < ε),
      ∃ (m : ℕ) (c : Fin m → ℝ) (W : Fin m → EuclideanSpace ℝ (Fin n))
        (b : Fin m → ℝ),
        ∀ x ∈ K, |f x - ∑ i, c i * σ (@inner ℝ _ _ (W i) x + b i)| < ε := by
  intro n K hK σ hσ hnp f hf ε hε
  have hexp : UniversalApprox.sigmaApprox σ Real.exp :=
    UniversalApprox.sigmaApprox_of_continuous σ hσ hnp Real.exp
      Real.continuous_exp
  have hnet : UniversalApprox.netApproxOn σ K f := by
    refine UniversalApprox.netApproxOn_of_near σ (fun ε' hε' => ?_)
    obtain ⟨m, a, v, herr⟩ := UniversalApprox.exists_expSum_near hK hf hε'
    refine ⟨fun x => ∑ j, a j * Real.exp (inner ℝ (v j) x), ?_, fun x hx => ?_⟩
    · refine UniversalApprox.netApproxOn_sum σ K Finset.univ
        (fun j x => a j * Real.exp (inner ℝ (v j) x)) ?_
      intro j _
      have hridge := UniversalApprox.netApproxOn_ridge σ Real.exp hexp hK (v j)
      exact UniversalApprox.netApproxOn_const_mul σ (a j) hridge
    · exact herr x hx
  obtain ⟨m, c, W, b, h⟩ := hnet ε hε
  exact ⟨m, c, W, b, h⟩

end MetaMathlibExt
