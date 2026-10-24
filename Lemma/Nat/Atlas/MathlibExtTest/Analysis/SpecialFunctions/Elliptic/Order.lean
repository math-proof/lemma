import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Analysis.SpecialFunctions.Elliptic.Order
open scoped Topology


namespace PeriodPair

/--
[order_inv_sub_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemmas. Only the behavior near `a` is used. -/
private lemma order_inv_sub_self (a : ℂ) :
  meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹) a = -1 := by
  have h1 : meromorphicOrderAt (fun z : ℂ => z - a) a = 1 :=
    meromorphicOrderAt_id_sub_const
  have hinv : (fun z : ℂ => (z - a)⁻¹) = (fun z : ℂ => z - a)⁻¹ := rfl
  rw [hinv, meromorphicOrderAt_inv, h1]

end PeriodPair

namespace PeriodPair

/--
[mult_inv_sub_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma mult_inv_sub_self (a : ℂ) :
  poleMultiplicity (fun z : ℂ => (z - a)⁻¹) a = 1 := by
  unfold poleMultiplicity
  rw [order_inv_sub_self a]
  rfl

end PeriodPair

namespace PeriodPair

/--
[not_differentiableAt_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
if it existed, would have to agree (as a real-linear map) with `conjCLE`, which
is not complex-linear: it fixes `1` but negates `Complex.I`. -/
private lemma not_differentiableAt_conj (b : ℂ) :
  ¬ DifferentiableAt ℂ (⇑(starRingEnd ℂ)) b := by
  intro h
  have hR := h.hasFDerivAt.restrictScalars ℝ
  have hconj : HasFDerivAt (⇑(starRingEnd ℂ))
    (Complex.conjCLE.toContinuousLinearMap) b :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have heq : (fderiv ℂ (⇑(starRingEnd ℂ)) b).restrictScalars ℝ =
    Complex.conjCLE.toContinuousLinearMap := hR.unique hconj
  have h1 : fderiv ℂ (⇑(starRingEnd ℂ)) b 1 = (starRingEnd ℂ) (1 : ℂ) := by
    have hcon := DFunLike.congr_fun heq (1 : ℂ)
    simpa using hcon
  have hI : fderiv ℂ (⇑(starRingEnd ℂ)) b Complex.I = (starRingEnd ℂ) Complex.I := by
    have hcon := DFunLike.congr_fun heq Complex.I
    simpa using hcon
  have hlin : fderiv ℂ (⇑(starRingEnd ℂ)) b Complex.I
    = Complex.I • fderiv ℂ (⇑(starRingEnd ℂ)) b 1 := by
    have hIb : Complex.I • (1 : ℂ) = Complex.I := by simp
    conv_lhs => rw [← hIb]
    rw [map_smul]
  have hcon : (starRingEnd ℂ) Complex.I
    = Complex.I • (starRingEnd ℂ) (1 : ℂ) := by
    rwa [← hI, ← h1]
  have hneg : -Complex.I = Complex.I := by simpa using hcon
  have hsum : Complex.I + Complex.I = 0 := by linear_combination -hneg
  have hI0 : Complex.I = 0 := by
    have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination hsum
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact Complex.I_ne_zero hI0

end PeriodPair

namespace PeriodPair

/--
[not_analyticAt_conj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma not_analyticAt_conj (y : ℂ) : ¬ AnalyticAt ℂ (⇑(starRingEnd ℂ)) y :=
  fun hy => not_differentiableAt_conj y hy.differentiableAt

end PeriodPair

namespace PeriodPair

/--
[poleWithConjBranch_not_meromorphicAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
there would force analyticity at some point of the conjugation ball, where the
function locally equals conjugation, contradicting nowhere-analyticity of
conjugation. The contradiction uses the whole ball, not a single value. -/
private lemma poleWithConjBranch_not_meromorphicAt :
  ¬ MeromorphicAt poleWithConjBranch 1 := by
  intro hf
  have hana := hf.eventually_analyticAt
  have hball_nhds : Metric.ball (1 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (1 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  have hmem : ∀ᶠ y in 𝓝[≠] (1 : ℂ), y ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds hball_nhds
  obtain ⟨y, hy_ana, hy_ball⟩ := (hana.and hmem).exists
  have heq : poleWithConjBranch =ᶠ[𝓝 y] (⇑(starRingEnd ℂ)) := by
    filter_upwards [IsOpen.mem_nhds Metric.isOpen_ball hy_ball] with z hz
    unfold poleWithConjBranch
    rw [ite_eq_left hz]
  exact not_analyticAt_conj y (hy_ana.congr heq)

end PeriodPair

/--
[poleWithConjBranch_eq_near_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
positive distance away from the conjugation ball around `1`. -/
private lemma poleWithConjBranch_eq_near_zero :
  poleWithConjBranch =ᶠ[𝓝 (0 : ℂ)] (fun z : ℂ => (z - 0)⁻¹) := by
  have h01 : dist (0 : ℂ) 1 = 1 := by rw [dist_comm, dist_zero_right, norm_one]
  have hnbhd : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [hnbhd] with z hz
  have hz_out : z ∉ Metric.ball (1 : ℂ) (1 / 2 : ℝ) := by
    rw [Metric.mem_ball] at hz ⊢
    have htri := dist_triangle (0 : ℂ) z (1 : ℂ)
    rw [h01, dist_comm (0 : ℂ) z] at htri
    linarith
  change poleWithConjBranch z = (z - 0)⁻¹
  unfold poleWithConjBranch
  exact ite_eq_right hz_out



-- created on 2026-10-23
