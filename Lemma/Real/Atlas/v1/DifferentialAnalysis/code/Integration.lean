import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.DifferentialAnalysis.code.Integration.Part2
open MeasureTheory ENNReal Set NormedSpaces Integration MonotoneConvergence
open scoped ENNReal
open MeasureTheory Filter ENNReal Topology


namespace NormedSpaces

/--
[Lp_isBanachSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma Lp_isBanachSpace
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
  {p : ENNReal}
  [Fact (1 ≤ p)] :
-- imply
  IsBanachSpace ℝ (Lp E p μ) :=
-- proof
  Lp.instCompleteSpace
open scoped ENNReal
section MinkowskiInequality

end NormedSpaces

namespace NormedSpaces

/--
[minkowski_inequality_eLpNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma minkowski_inequality_eLpNorm
  {m : MeasurableSpace α}
  {μ : Measure α}
  [NormedAddCommGroup E]
  {p : ENNReal}
  {f g : α → E}
-- given
  (hp_one : 1 < p)
  (hf : MemLp f p μ)
  (hg : MemLp g p μ) :
-- imply
  eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
-- proof
  eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp_one.le
end NormedSpaces
namespace Integration
section LIntegralZero


namespace Integration

/--
[lintegral_eq_zero_iff_measure_pos_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma lintegral_eq_zero_iff_measure_pos_eq_zero
  [MeasurableSpace α]
  {μ : Measure α}
  {f : α → ENNReal}
  {E : Set α}
-- given
  (hf : Measurable f)
  (hE : MeasurableSet E) :
-- imply
  ∫⁻ x in E, f x ∂μ = 0 ↔ μ {x ∈ E | 0 < f x} = 0 := by
-- proof
  rw [setLIntegral_eq_zero_iff hE hf, ae_iff]
  have : {a | ¬(a ∈ E → f a = 0)} = {x ∈ E | 0 < f x} := by
    ext x
    simp only [mem_setOf_eq, _root_.not_imp, pos_iff_ne_zero, ne_eq]
  rw [this]
end LIntegralZero

end Integration

namespace Integration

/--
[rpow_mul_rpow_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma rpow_mul_rpow_le_add
  {a b γ : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hγ₀ : 0 < γ)
  (hγ₁ : γ < 1) :
-- imply
  a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b :=
-- proof
  Real.geom_mean_le_arith_mean2_weighted hγ₀.le (by linarith) ha hb (by linarith)

end Integration

namespace Integration

/--
[rpow_mul_rpow_lt_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma rpow_mul_rpow_lt_add
  {a b γ : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hγ₀ : 0 < γ)
  (hγ₁ : γ < 1)
  (hab : a ≠ b) :
-- imply
  a ^ γ * b ^ (1 - γ) < γ * a + (1 - γ) * b := by
-- proof
  open Finset in
  let w : Fin 2 → ℝ := ![γ, 1 - γ]
  let z : Fin 2 → ℝ := ![a, b]
  have hw : ∀ i ∈ (univ : Finset (Fin 2)), 0 < w i := by
    intro i _; fin_cases i
    · simp [w]; exact hγ₀
    · simp [w]; linarith
  have hw' : ∑ i ∈ (univ : Finset (Fin 2)), w i = 1 := by
    simp [Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz : ∀ i ∈ (univ : Finset (Fin 2)), 0 ≤ z i := by
    intro i _; fin_cases i
    · simp [z]; exact ha
    · simp [z]; exact hb
  have key := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos univ w z hw hw' hz).mpr
    ⟨0, mem_univ _, 1, mem_univ _, by simp [z]; exact hab⟩
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, w, z] at key
  simpa using key

end Integration

namespace Integration

/--
[rpow_mul_rpow_eq_add_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma rpow_mul_rpow_eq_add_iff
  {a b γ : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hγ₀ : 0 < γ)
  (hγ₁ : γ < 1) :
-- imply
  a ^ γ * b ^ (1 - γ) = γ * a + (1 - γ) * b ↔ a = b := by
-- proof
  constructor
  · intro heq
    by_contra hab
    exact absurd heq (ne_of_lt (rpow_mul_rpow_lt_add a b γ ha hb hγ₀ hγ₁ hab))
  · intro heq
    subst heq
    obtain rfl | ha' := eq_or_lt_of_le ha
    · simp [Real.zero_rpow (ne_of_gt hγ₀), Real.zero_rpow (by linarith : (1 : ℝ) - γ ≠ 0)]
    · rw [← Real.rpow_add ha', add_sub_cancel, Real.rpow_one]; ring

end Integration

namespace Integration

/--
[rpow_mul_rpow_le_add_and_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma rpow_mul_rpow_le_add_and_eq_iff
  {a b γ : ℝ}
-- given
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hγ₁ : 0 < γ)
  (hγ₂ : γ < 1) :
-- imply
  a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b ∧ (a ^ γ * b ^ (1 - γ) = γ * a + (1 - γ) * b ↔ a = b) :=
-- proof
  ⟨rpow_mul_rpow_le_add a b γ ha hb hγ₁ hγ₂, rpow_mul_rpow_eq_add_iff a b γ ha hb hγ₁ hγ₂⟩

end Integration

namespace Integration

/--
[holder_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma holder_inequality
  [MeasurableSpace α]
  {μ : Measure α}
  {p q : ℝ}
  {f g : α → ℝ}
-- given
  (hpq : p.HolderConjugate q)
  (hf : MemLp f (ENNReal.ofReal p) μ)
  (hg : MemLp g (ENNReal.ofReal q) μ) :
-- imply
  |∫ a, f a * g a ∂μ| ≤ (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
-- proof
  calc |∫ a, f a * g a ∂μ|
    _ ≤ ∫ a, |f a * g a| ∂μ := abs_integral_le_integral_abs
    _ = ∫ a, |f a| * |g a| ∂μ := by
      congr 1; ext a; exact abs_mul (f a) (g a)
    _ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
      simp_rw [← Real.norm_eq_abs]
    _ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ = (∫ a, |f a| ^ p ∂μ) ^ (1 / p) * (∫ a, |g a| ^ q ∂μ) ^ (1 / q) := by
      simp_rw [Real.norm_eq_abs]

end Integration

namespace Integration

/--
[fatou_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma fatou_lemma
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n)) :
-- imply
  ∫⁻ a, Filter.atTop.liminf (fun n => f n a) ∂μ ≤ Filter.atTop.liminf (fun n => ∫⁻ a, f n a ∂μ) :=
-- proof
  lintegral_liminf_le hf
end Integration
namespace MonotoneConvergence
open MeasureTheory Filter ENNReal Topology


namespace MonotoneConvergence

/--
[monotone_convergence_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma monotone_convergence_measurable
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n)) :
-- imply
  Measurable (fun x => ⨆ n, f n x) :=
-- proof
  Measurable.iSup hf

end MonotoneConvergence

namespace MonotoneConvergence

/--
[monotone_convergence_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma monotone_convergence_iSup
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
  {E : Set α}
-- given
  (hf : ∀ n, Measurable (f n))
  (h_mono : Monotone f) :
-- imply
  ∫⁻ x in E, (⨆ n, f n x) ∂μ = ⨆ n, ∫⁻ x in E, f n x ∂μ :=
-- proof
  lintegral_iSup hf h_mono

end MonotoneConvergence

namespace MonotoneConvergence

/--
[monotone_convergence_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Integration.lean)
-/
@[path]
lemma monotone_convergence_tendsto
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
  {E : Set α}
-- given
  (hf : ∀ n, Measurable (f n))
  (h_mono : Monotone f) :
-- imply
  Tendsto (fun n => ∫⁻ x in E, f n x ∂μ) atTop (𝓝 (∫⁻ x in E, (⨆ n, f n x) ∂μ)) := by
-- proof
  rw [monotone_convergence_iSup hf h_mono]
  apply tendsto_atTop_iSup
  intro i j hij
  exact lintegral_mono (h_mono hij)

end MonotoneConvergence


-- created on 2026-10-23
