import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part3
open Complex Filter Set SmoothCurve PiecewiseSmoothCurve Residue
open scoped Topology
open Filter
open Set
open MeasureTheory
open parameter interval $(a, b)$. -/
open MeasureTheory Finset
open scoped Topology Classical


/--
[liouville_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma liouville_theorem
  {f : ℂ → ℂ}
-- given
  (hf : IsEntire f)
  (hb : IsBounded (range f)) :
-- imply
  ∃ c : ℂ, f = Function.const ℂ c :=
-- proof
  hf.exists_eq_const_of_bounded hb
open Filter
open scoped Topology

/--
[hasZeroOfOrder_iff_meromorphicOrderAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma hasZeroOfOrder_iff_meromorphicOrderAt
  {k : ℕ}
  {f : ℂ → ℂ}
  {z₀ : ℂ}
-- given
  (hf : MeromorphicAt f z₀) :
-- imply
  HasZeroOfOrder k f z₀ ↔ 0 < k ∧ meromorphicOrderAt f z₀ = (k : ℤ) := by
-- proof
  constructor
  · rintro ⟨hk, g, hg_an, hg_ne, hg_eq⟩
    refine ⟨hk, (meromorphicOrderAt_eq_int_iff hf).mpr ?_⟩
    exact ⟨g, hg_an, hg_ne, by
      filter_upwards [hg_eq] with z hz
      simp only [smul_eq_mul, zpow_natCast, hz]⟩
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
    exact ⟨g, hg_an, hg_ne, by
      filter_upwards [hg_eq] with z hz
      simp only [smul_eq_mul, zpow_natCast] at hz
      exact hz⟩

/--
[hasPoleOfOrder_iff_meromorphicOrderAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma hasPoleOfOrder_iff_meromorphicOrderAt
  {k : ℕ}
  {f : ℂ → ℂ}
  {z₀ : ℂ}
-- given
  (hf : MeromorphicAt f z₀) :
-- imply
  HasPoleOfOrder k f z₀ ↔ 0 < k ∧ meromorphicOrderAt f z₀ = (-↑k : ℤ) := by
-- proof
  unfold HasPoleOfOrder
  rw [hasZeroOfOrder_iff_meromorphicOrderAt hf.inv]
  constructor
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    have h := meromorphicOrderAt_inv (f := f) (x := z₀)
    rw [hord] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  · rintro ⟨hk, hord⟩
    refine ⟨hk, ?_⟩
    have h := meromorphicOrderAt_inv (f := f) (x := z₀)
    rw [hord] at h
    push_cast [neg_neg] at h
    exact h

/--
[isMeromorphicOn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma isMeromorphicOn_iff
  {f : ℂ → ℂ}
  {Ω : Set ℂ} :
-- imply
  IsMeromorphicOn f Ω ↔ MeromorphicOn f Ω :=
-- proof
  Iff.rfl

namespace SmoothCurve

/--
[continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma continuousOn
  {γ : SmoothCurve} :
-- imply
  ContinuousOn γ.toFun (Icc γ.a γ.b) :=
-- proof
  γ.contDiffOn.continuousOn
end SmoothCurve
namespace SmoothCurve
open MeasureTheory

end SmoothCurve

namespace SmoothCurve

/--
[contourIntegral_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma contourIntegral_def
  {f : ℂ → ℂ}
  {γ : SmoothCurve} :
-- imply
  γ.contourIntegral f = ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t :=
-- proof
  rfl

end SmoothCurve

namespace PiecewiseSmoothCurve

/--
[contourIntegral_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma contourIntegral_def
  {f : ℂ → ℂ}
  {γ : PiecewiseSmoothCurve} :
-- imply
  γ.contourIntegral f = ∑ i : Fin γ.n, (γ.pieces i).contourIntegral f :=
-- proof
  rfl

end PiecewiseSmoothCurve

namespace SmoothCurve

/--
[contourIntegral_eq_sub_of_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma contourIntegral_eq_sub_of_deriv
  {F : ℂ → ℂ}
  {γ : SmoothCurve}
-- given
  (hF : ∀ t ∈ Set.uIcc γ.a γ.b, DifferentiableAt ℂ F (γ.toFun t))
  (hγ : ∀ t ∈ Set.uIcc γ.a γ.b, DifferentiableAt ℝ γ.toFun t)
  (hint : IntervalIntegrable (fun t => deriv F (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
-- imply
  γ.contourIntegral (deriv F) = F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
-- proof
  unfold contourIntegral
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hF t ht).hasDerivAt.comp t (hγ t ht).hasDerivAt) hint
end SmoothCurve
namespace PiecewiseSmoothCurve
open MeasureTheory Finset


namespace PiecewiseSmoothCurve

/--
[telescoping_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma telescoping_sum
  {n : ℕ}
  {G_b G_a : Fin n → ℂ}
-- given
  (hn : 0 < n)
  (hconnect : ∀ (i : Fin n) (hi : i.val + 1 < n), G_b i = G_a ⟨i.val + 1, hi⟩) :
-- imply
  ∑ i : Fin n, (G_b i - G_a i) = G_b ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩ - G_a ⟨0, hn⟩ := by
-- proof
  let g : ℕ → ℂ := fun j =>
    if hj : j < n then G_a ⟨j, hj⟩ else G_b ⟨n - 1, Nat.sub_one_lt_of_lt hn⟩
  have hterms : ∀ i : Fin n, G_b i - G_a i = g (i.val + 1) - g i.val := by
    intro ⟨i, hi⟩
    simp only [g, hi, dite_true]
    by_cases h : i + 1 < n
    · simp only [h, dite_true]
      rw [← hconnect ⟨i, hi⟩ h]
    · simp only [h, dite_false]
      have hieq : i = n - 1 := by omega
      subst hieq
      rfl
  conv_lhs =>
    arg 2
    ext i
    rw [hterms i]
  rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j), Finset.sum_range_sub g]
  simp only [g, hn, dite_true, Nat.lt_irrefl, dite_false]

end PiecewiseSmoothCurve

namespace PiecewiseSmoothCurve

/--
[theorem_14_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma theorem_14_13
  {F : ℂ → ℂ}
  {γ : PiecewiseSmoothCurve}
-- given
  (hF : ∀ i : Fin γ.n, ∀ t ∈ Set.uIcc (γ.pieces i).a (γ.pieces i).b, DifferentiableAt ℂ F ((γ.pieces i).toFun t))
  (hγ : ∀ i : Fin γ.n, ∀ t ∈ Set.uIcc (γ.pieces i).a (γ.pieces i).b, DifferentiableAt ℝ (γ.pieces i).toFun t)
  (hint : ∀ i : Fin γ.n, IntervalIntegrable (fun t => deriv F ((γ.pieces i).toFun t) * deriv (γ.pieces i).toFun t) volume (γ.pieces i).a (γ.pieces i).b) :
-- imply
  γ.contourIntegral (deriv F) = F ((γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).toFun (γ.pieces ⟨γ.n - 1, Nat.sub_one_lt_of_lt γ.hn⟩).b) - F ((γ.pieces ⟨0, γ.hn⟩).toFun (γ.pieces ⟨0, γ.hn⟩).a) := by
-- proof
  unfold contourIntegral
  simp_rw [fun i => SmoothCurve.contourIntegral_eq_sub_of_deriv F (γ.pieces i)
    (hF i) (hγ i) (hint i)]
  exact telescoping_sum γ.n γ.hn _ _ (fun i hi => congrArg F (γ.continuous_join i hi))

end PiecewiseSmoothCurve

/--
[theorem_14_14_circle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma theorem_14_14_circle
  {R : ℝ}
  {c : ℂ}
  {f : ℂ → ℂ}
-- given
  (hR : 0 ≤ R)
  (hf : DifferentiableOn ℂ f (closedBall c R)) :
-- imply
  (∮ z in C(c, R), f z) = 0 :=
-- proof
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty hf.continuousOn
    (fun _z ⟨hz, _⟩ => hf.differentiableAt (closedBall_mem_nhds_of_mem hz))
namespace Residue
open Complex Filter
open scoped Topology Classical

namespace Residue

/--
[residue_of_not_meromorphicAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma residue_of_not_meromorphicAt
  {f : ℂ → ℂ}
  {z₀ : ℂ}
-- given
  (hf : ¬MeromorphicAt f z₀) :
-- imply
  residue f z₀ = 0 :=
-- proof
  dif_neg hf

end Residue

namespace Residue

/--
[residue_eq_zero_of_analyticAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma residue_eq_zero_of_analyticAt
  {f : ℂ → ℂ}
  {z₀ : ℂ}
-- given
  (hf : AnalyticAt ℂ f z₀) :
-- imply
  residue f z₀ = 0 := by
-- proof
  unfold residue
  have hm : MeromorphicAt f z₀ := hf.meromorphicAt
  rw [dif_pos hm]
  split_ifs with hn
  · rfl
  · suffices h0 : iteratedDeriv (hm.choose - 1)
    (fun z => (z - z₀) ^ hm.choose • f z) z₀ = 0 by
    rw [h0, zero_div]
    have smul_eq : (fun z => (z - z₀) ^ hm.choose • f z) =
      (fun z => (z - z₀) ^ hm.choose * f z) := by
      ext z; simp [smul_eq_mul]
    rw [smul_eq]
    set n := hm.choose
    have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
    have hg : AnalyticAt ℂ (fun z => (z - z₀) ^ n * f z) z₀ := by
      rw [← smul_eq]; exact hm.choose_spec
    have hord : (n : ℕ∞) ≤ analyticOrderAt (fun z => (z - z₀) ^ n * f z) z₀ := by
      rw [show (fun z => (z - z₀) ^ n * f z) = ((fun z => z - z₀) ^ n * f) from by
        ext; simp [Pi.pow_apply, Pi.mul_apply]]
      rw [analyticOrderAt_mul
        (AnalyticAt.pow (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀) n) hf]
      rw [analyticOrderAt_pow (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀)]
      have h1 : (1 : ℕ∞) ≤ analyticOrderAt (fun z => z - z₀) z₀ := by
        rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl]
        rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
          (by fun_prop : AnalyticAt ℂ (fun z => z - z₀) z₀)]
        intro i hi; interval_cases i; simp [iteratedDeriv_zero]
      calc (n : ℕ∞) = n • 1 + 0 := by simp
        _ ≤ n • analyticOrderAt (fun z => z - z₀) z₀ + analyticOrderAt f z₀ := by
          apply add_le_add
          · exact smul_le_smul_of_nonneg_left h1 (Nat.zero_le n)
          · exact zero_le _
    exact ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp hord)
      (n - 1) (by omega)
end Residue
export Residue (residue)

end Residue

/--
[isMeromorphicOn_g_f'_over_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma isMeromorphicOn_g_f'_over_f
  {f g : ℂ → ℂ}
  {Ω : Set ℂ}
-- given
  (hΩ : IsOpen Ω)
  (hf_mero : IsMeromorphicOn f Ω)
  (hg_holo : HolomorphicOn g Ω) :
-- imply
  IsMeromorphicOn (fun z => g z * (deriv f z / f z)) Ω := by
-- proof
  intro z hz
  have hf_z : MeromorphicAt f z := hf_mero z hz
  have hg_mero : MeromorphicAt g z :=
    (hg_holo.analyticAt (hΩ.mem_nhds hz)).meromorphicAt
  have key : MeromorphicAt (g • (deriv f • f⁻¹)) z :=
    hg_mero.smul (hf_z.deriv.smul hf_z.inv)
  refine key.congr (Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_)
  filter_upwards with w
  simp [smul_eq_mul, div_eq_mul_inv]

/--
[analyticAt_g_f'_over_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexAnalysis.lean)
-/
@[path]
lemma analyticAt_g_f'_over_f
  {f g : ℂ → ℂ}
  {z : ℂ}
  {Ω : Set ℂ}
-- given
  (hΩ : IsOpen Ω)
  (hg_holo : HolomorphicOn g Ω)
  (hz : z ∈ Ω)
  (hf_an : AnalyticAt ℂ f z)
  (hf_nz : f z ≠ 0) :
-- imply
  AnalyticAt ℂ (fun z => g z * (deriv f z / f z)) z := by
-- proof
  have hg_an : AnalyticAt ℂ g z := hg_holo.analyticAt (hΩ.mem_nhds hz)
  exact hg_an.fun_mul (hf_an.deriv.fun_div hf_an hf_nz)
/-- **Theorem 14.17 (Generalized argument principle).**  Let $\gamma$ be a
positively oriented, simple, closed piecewise smooth curve in $\Omega$, let $g$
be holomorphic on $\Omega$, and let $f$ be meromorphic on $\Omega$ with no
zeros or poles on $\gamma$ and finitely many zeros/poles $p_k$ of order
$m_k \in \mathbb{Z}$ inside $\gamma$.  Then
$\int_\gamma g(z) \frac{f'(z)}{f(z)} \, dz = 2 \pi i \sum_k g(p_k) m_k$. -/


-- created on 2026-10-23
