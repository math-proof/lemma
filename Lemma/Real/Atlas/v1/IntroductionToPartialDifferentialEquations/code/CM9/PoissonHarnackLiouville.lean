import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville
open Set Real MeasureTheory Filter Topology PoissonHarnack


namespace PoissonHarnack

/--
[kelvinReflection_sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma kelvinReflection_sub_eq
  {p x y : Fin 3 → ℝ}
  {R : ℝ} :
-- imply
  kelvinReflection p R x - y = fun i => R^2 / CM8.euclidNorm (x - p)^2 * (x i - p i) - (y i - p i) := by
-- proof
  ext i; simp [kelvinReflection, Pi.sub_apply]; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[greenBall_eq_explicit_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma greenBall_eq_explicit_formula
  {R : ℝ}
  {p x y : Fin 3 → ℝ} :
-- imply
  greenBall R p x y = greenBallFormula R p x y := by
-- proof
  unfold greenBall greenBallFormula CM8.Phi3
  rw [kelvinReflection_sub_eq]
  ring

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_sq
  {v : Fin 3 → ℝ} :
-- imply
  CM8.euclidNorm v ^ 2 = normSq v := by
-- proof
  unfold CM8.euclidNorm normSq; exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq_kelvin_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq_kelvin_sub
  {p x σ : Fin 3 → ℝ}
  {R : ℝ} :
-- imply
  normSq (kelvinReflection p R x - σ) = normSq (fun i => p i + R ^ 2 / CM8.euclidNorm (x - p) ^ 2 * (x i - p i) - σ i) := by
-- proof
  unfold normSq; congr 1; ext i; simp [kelvinReflection, Pi.sub_apply]; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq_diff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq_diff_eq
  {x σ p : Fin 3 → ℝ} :
-- imply
  normSq (x - σ) = normSq (x - p) - 2 * innerProd3 (x - p) (σ - p) + normSq (σ - p) := by
-- proof
  unfold normSq innerProd3; simp only [Fin.sum_univ_three, Pi.sub_apply]; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq_kr_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq_kr_expand
  {p x σ : Fin 3 → ℝ}
  {c : ℝ} :
-- imply
  normSq (fun i => p i + c * (x i - p i) - σ i) = c ^ 2 * normSq (x - p) - 2 * c * innerProd3 (x - p) (σ - p) + normSq (σ - p) := by
-- proof
  unfold normSq innerProd3; simp only [Fin.sum_univ_three, Pi.sub_apply]; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq_product_eq
  {p x σ : Fin 3 → ℝ}
  {R : ℝ}
-- given
  (hS : normSq (x - p) ≠ 0)
  (hσ : normSq (σ - p) = R ^ 2) :
-- imply
  normSq (kelvinReflection p R x - σ) * normSq (x - p) = R ^ 2 * normSq (x - σ) := by
-- proof
  rw [normSq_kelvin_sub, show R ^ 2 / CM8.euclidNorm (x - p) ^ 2 = R ^ 2 / normSq (x - p) from
    by rw [euclidNorm_sq]]
  rw [normSq_kr_expand, hσ, normSq_diff_eq x σ p, hσ]
  field_simp; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[norm_product_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma norm_product_identity
  {p x σ : Fin 3 → ℝ}
  {R : ℝ}
-- given
  (hR : 0 < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) = R * CM8.euclidNorm (x - σ) := by
-- proof
  have hS : normSq (x - p) ≠ 0 := by
    intro h; rw [← euclidNorm_sq] at h; nlinarith [sq_nonneg (CM8.euclidNorm (x - p))]
  have hσ2 : normSq (σ - p) = R ^ 2 := by
    have := euclidNorm_sq (σ - p); rw [hσ] at this; linarith
  have h_sq := normSq_product_eq p x σ R hS hσ2
  have lhs_sq : (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p)) ^ 2 =
    normSq (kelvinReflection p R x - σ) * normSq (x - p) := by
    rw [mul_pow, euclidNorm_sq, euclidNorm_sq]
  have rhs_sq : (R * CM8.euclidNorm (x - σ)) ^ 2 = R ^ 2 * normSq (x - σ) := by
    rw [mul_pow, euclidNorm_sq]
  have lhs_nn : 0 ≤ CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have rhs_nn : 0 ≤ R * CM8.euclidNorm (x - σ) := mul_nonneg (le_of_lt hR) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p)),
    sq_abs (R * CM8.euclidNorm (x - σ)),
    abs_of_nonneg lhs_nn, abs_of_nonneg rhs_nn,
    lhs_sq, rhs_sq, h_sq,
    sq_nonneg (CM8.euclidNorm (kelvinReflection p R x - σ) * CM8.euclidNorm (x - p) -
      R * CM8.euclidNorm (x - σ))]

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_zero_imp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_zero_imp_eq
  {a b : Fin 3 → ℝ}
-- given
  (h : CM8.euclidNorm (a - b) = 0) :
-- imply
  a = b := by
-- proof
  unfold CM8.euclidNorm at h
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h
  ext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((a - b) j))).mp h i
    (Finset.mem_univ i)
  simp [Pi.sub_apply] at this; linarith [this]
set_option maxHeartbeats 400000 in

end PoissonHarnack

namespace PoissonHarnack

/--
[greenBall_boundary_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma greenBall_boundary_vanish
  {R : ℝ}
  {p : Fin 3 → ℝ}
  {x : Fin 3 → ℝ}
  {σ : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hx : CM8.euclidNorm (x - p) < R)
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  greenBall R p x σ = 0 := by
-- proof
  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith
  have h_norm := norm_product_identity p x σ R hR hxp hσ
  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith
  unfold greenBall CM8.Phi3
  field_simp
  linarith [h_norm]

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_continuous'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_continuous'
  {n : ℕ} :
-- imply
  Continuous (fun x : Fin n → ℝ => CM8.euclidNorm x) := by
-- proof
  unfold CM8.euclidNorm
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2))

end PoissonHarnack

namespace PoissonHarnack

/--
[abs_component_le_euclidNorm'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma abs_component_le_euclidNorm'
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  |x i| ≤ CM8.euclidNorm x := by
-- proof
  unfold CM8.euclidNorm
  rwa [← Real.sqrt_sq_eq_abs]
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_smul'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_smul'
  {n : ℕ}
  {c : ℝ}
  {x : Fin n → ℝ} :
-- imply
  CM8.euclidNorm (c • x) = |c| * CM8.euclidNorm x := by
-- proof
  unfold CM8.euclidNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end PoissonHarnack

namespace PoissonHarnack

/--
[boundary_in_closure'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma boundary_in_closure'
  {n : ℕ}
  {R : ℝ}
  {p z : Fin n → ℝ}
-- given
  (hR : 0 < R)
  (heq : CM8.euclidNorm (z - p) = R) :
-- imply
  z ∈ closure {w : Fin n → ℝ | CM8.euclidNorm (w - p) < R} := by
-- proof
  rw [Metric.mem_closure_iff]
  intro ε hε
  set M := ‖z - p‖ + 1
  have hM : 0 < M := by positivity
  set δ := min (ε / (2 * M)) (1/2 : ℝ)
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set w := p + (1 - δ) • (z - p)
  refine ⟨w, ?_, ?_⟩
  · show CM8.euclidNorm (w - p) < R
    have hw_sub : w - p = (1 - δ) • (z - p) := by simp [w, add_sub_cancel_left]
    rw [hw_sub, euclidNorm_smul', heq, abs_of_pos (by linarith : (0 : ℝ) < 1 - δ)]
    nlinarith
  · have hz_sub_w : z - w = δ • (z - p) := by simp [w]; ext i; simp; ring
    calc dist z w = ‖z - w‖ := dist_eq_norm z w
      _ = ‖δ • (z - p)‖ := by rw [hz_sub_w]
      _ = |δ| * ‖z - p‖ := norm_smul δ (z - p)
      _ = δ * ‖z - p‖ := by rw [abs_of_pos hδ_pos]
      _ < δ * M := by nlinarith [norm_nonneg (z - p)]
      _ ≤ (ε / (2 * M)) * M := by nlinarith [min_le_left (ε / (2 * M)) (1/2 : ℝ)]
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

end PoissonHarnack

namespace PoissonHarnack

/--
[isOpen_euclidBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma isOpen_euclidBall
  {R : ℝ}
  {p : Fin 3 → ℝ} :
-- imply
  IsOpen {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} :=
-- proof
  (euclidNorm_continuous'.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Iio

end PoissonHarnack

namespace PoissonHarnack

/--
[isBounded_euclidBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma isBounded_euclidBall
  {R : ℝ}
  {p : Fin 3 → ℝ}
-- given
  (hR : 0 < R) :
-- imply
  Bornology.IsBounded {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} := by
-- proof
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := p) (r := R))
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  simp only [Metric.mem_closedBall]
  rw [dist_pi_le_iff (le_of_lt hR)]
  intro i
  calc dist (z i) (p i) = |z i - p i| := Real.dist_eq _ _
    _ = |(z - p) i| := by simp
    _ ≤ CM8.euclidNorm (z - p) := abs_component_le_euclidNorm' _ i
    _ ≤ R := le_of_lt hz

end PoissonHarnack

namespace PoissonHarnack

/--
[frontier_euclidBall_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma frontier_euclidBall_eq
  {R : ℝ}
  {p : Fin 3 → ℝ}
-- given
  (hR : 0 < R) :
-- imply
  frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R} = {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) = R} := by
-- proof
  set f : (Fin 3 → ℝ) → ℝ := fun z => CM8.euclidNorm (z - p)
  set S := {z : Fin 3 → ℝ | f z < R}
  have hf : Continuous f := euclidNorm_continuous'.comp (continuous_id.sub continuous_const)
  have hS_open : IsOpen S := hf.isOpen_preimage _ isOpen_Iio
  have hcl : closure S = {z | f z ≤ R} := by
    ext z; simp only [Set.mem_setOf_eq]; constructor
    · intro hz
      by_contra h; push Not at h
      have : {w | R < f w} ∈ nhds z := (hf.isOpen_preimage _ isOpen_Ioi).mem_nhds h
      obtain ⟨w, hwR, hwS⟩ := mem_closure_iff_nhds.mp hz _ this
      simp only [Set.mem_setOf_eq, S] at hwR hwS; linarith
    · intro hle
      obtain hlt | heq := lt_or_eq_of_le hle
      · exact subset_closure hlt
      · exact boundary_in_closure' R hR p z heq
  rw [frontier, interior_eq_iff_isOpen.mpr hS_open, hcl]
  ext z; simp only [Set.mem_diff, Set.mem_setOf_eq, S]; constructor
  · rintro ⟨hle, hlt⟩; linarith
  · intro heq; exact ⟨le_of_eq heq, by linarith⟩

end PoissonHarnack

namespace PoissonHarnack

/--
[fundSolN_continuousOn_frontier_euclidBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma fundSolN_continuousOn_frontier_euclidBall
  {R : ℝ}
  {p : Fin 3 → ℝ}
-- given
  (hR : 0 < R) :
-- imply
  ∀ x ∈ {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}, ContinuousOn (fun σ => CM8.FundSolN (x - σ)) (frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}) := by
-- proof
  intro x hx
  have heq : ∀ σ, CM8.FundSolN (x - σ) = CM8.Phi3 (x - σ) := fun σ => CM8.FundSolN_eq_Phi3 (x - σ)
  simp_rw [heq]
  simp only [CM8.Phi3]
  set F := frontier {z : Fin 3 → ℝ | CM8.euclidNorm (z - p) < R}
  have hF_eq : F = {z | CM8.euclidNorm (z - p) = R} := frontier_euclidBall_eq R hR p
  have hpos : ∀ σ ∈ F, CM8.euclidNorm (x - σ) > 0 := by
    intro σ hσ
    rw [hF_eq] at hσ
    simp only [Set.mem_setOf_eq] at hx hσ
    by_contra h
    push Not at h
    have h0 : CM8.euclidNorm (x - σ) = 0 := le_antisymm h (Real.sqrt_nonneg _)
    have hxσ : x = σ := by
      ext i
      have hsq : ∑ j : Fin 3, (x - σ) j ^ 2 = 0 := by
        unfold CM8.euclidNorm at h0
        exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg _)).mp h0
      have hi : (x - σ) i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((x - σ) j))).mp hsq i
          (Finset.mem_univ _)
      have : (x - σ) i = 0 := sq_eq_zero_iff.mp hi
      simp [Pi.sub_apply] at this; linarith
    rw [hxσ] at hx
    linarith
  have hcont_norm : ContinuousOn (fun σ => CM8.euclidNorm (x - σ)) F :=
    (euclidNorm_continuous'.comp (continuous_const.sub continuous_id)).continuousOn
  have hcont_denom : ContinuousOn (fun σ => 4 * Real.pi * CM8.euclidNorm (x - σ)) F :=
    continuousOn_const.mul hcont_norm
  have hne : ∀ σ ∈ F, 4 * Real.pi * CM8.euclidNorm (x - σ) ≠ 0 := by
    intro σ hσ
    have := hpos σ hσ
    positivity
  exact continuousOn_const.div hcont_denom hne

end PoissonHarnack

namespace PoissonHarnack

/--
[laplacian_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma laplacian_compat
  {u : (Fin 3 → ℝ) → ℝ}
  {x : Fin 3 → ℝ} :
-- imply
  CM7.Laplacian 3 u x = CM8.laplacian u x :=
-- proof
  rfl

end PoissonHarnack

namespace PoissonHarnack

/--
[greenBall_at_center](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma greenBall_at_center
  {R : ℝ}
  {p y : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hy : CM8.euclidNorm (y - p) = R) :
-- imply
  Filter.Tendsto (fun x => greenBall R p x y) (nhdsWithin p {x | 0 < CM8.euclidNorm (x - p)}) (nhds (-1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R))) := by
-- proof
  have h_target : -1 / (4 * Real.pi * CM8.euclidNorm (y - p)) + 1 / (4 * Real.pi * R) = 0 := by
    rw [hy]; ring
  rw [h_target]
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  have hmem : {x : Fin 3 → ℝ | CM8.euclidNorm (x - p) < R} ∈ nhds p := by
    have hcont : Continuous (fun x : Fin 3 → ℝ => CM8.euclidNorm (x - p)) := by
      unfold CM8.euclidNorm
      fun_prop
    apply hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds
    show CM8.euclidNorm (p - p) < R
    simp only [sub_self]
    unfold CM8.euclidNorm
    simp [hR]
  filter_upwards [hmem] with x' hx' hx'_pos
  exact greenBall_boundary_vanish R hR p x' y hx'_pos hx' hy

end PoissonHarnack

namespace PoissonHarnack

/--
[greenBall_at_center_eq_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma greenBall_at_center_eq_formula
  {R : ℝ}
  {p y : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hy : CM8.euclidNorm (y - p) = R) :
-- imply
  Filter.Tendsto (fun x => greenBall R p x y) (nhdsWithin p {x | 0 < CM8.euclidNorm (x - p)}) (nhds (greenBallFormula_at_center R p y)) :=
-- proof
greenBall_at_center R hR p y hy

end PoissonHarnack

namespace PoissonHarnack

/--
[outwardUnitNormal_ball_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma outwardUnitNormal_ball_spec
  {R : ℝ}
  {p σ : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  CM8.outwardUnitNormal {y | CM8.euclidNorm (y - p) < R} σ = fun i => (σ i - p i) / R :=
-- proof
  CM8.outwardUnitNormal_euclidBall_eq R hR p σ hσ

end PoissonHarnack

namespace PoissonHarnack

/--
[outwardUnitNormal_euclidBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma outwardUnitNormal_euclidBall
  {R : ℝ}
  {p σ : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  CM8.outwardUnitNormal {y | CM8.euclidNorm (y - p) < R} σ = fun i => (σ i - p i) / R :=
-- proof
  outwardUnitNormal_ball_spec R hR p σ hσ

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq3_pos'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq3_pos'
  {x : Fin 3 → ℝ}
-- given
  (hx : CM8.euclidNorm x ≠ 0) :
-- imply
  0 < normSq3' x := by
-- proof
  unfold normSq3' CM8.euclidNorm at *
  by_contra h; push Not at h
  exact hx (by rw [le_antisymm h (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]; simp)

end PoissonHarnack

namespace PoissonHarnack

/--
[hasFDerivAt_normSq3'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma hasFDerivAt_normSq3'
  {x : Fin 3 → ℝ} :
-- imply
  HasFDerivAt normSq3' (normSq3_CLM' x) x := by
-- proof
  unfold normSq3'
  rw [show (fun y : Fin 3 → ℝ => ∑ j : Fin 3, y j ^ 2) =
    ∑ j : Fin 3, (fun y : Fin 3 → ℝ => y j ^ 2) from by ext y; simp [Finset.sum_apply]]
  apply HasFDerivAt.sum; intro j _
  convert (hasFDerivAt_apply (𝕜 := ℝ) (ι := Fin 3) (F' := fun _ => ℝ) j x).pow 2 using 1
  simp [mul_comm]

end PoissonHarnack

namespace PoissonHarnack

/--
[hasDerivAt_neg_inv_4pi_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma hasDerivAt_neg_inv_4pi_sqrt
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  HasDerivAt (fun s => -1 / (4 * Real.pi * Real.sqrt s)) (1 / (8 * Real.pi * (Real.sqrt s) ^ 3)) s := by
-- proof
  have hsqrt_ne := ne_of_gt (Real.sqrt_pos.mpr hs)
  have h_h : HasDerivAt (fun r => -1 / (4 * Real.pi * r))
    ((-1/(4*Real.pi)) * (-(Real.sqrt s ^ 2)⁻¹)) (Real.sqrt s) := by
    convert (hasDerivAt_inv hsqrt_ne).const_mul (-1/(4*Real.pi)) using 1; ext r; ring
  convert h_h.comp s (Real.hasDerivAt_sqrt (ne_of_gt hs)) using 1
  field_simp; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[hasFDerivAt_Phi3_direct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma hasFDerivAt_Phi3_direct
  {y : Fin 3 → ℝ}
-- given
  (hy : CM8.euclidNorm y ≠ 0) :
-- imply
  HasFDerivAt CM8.Phi3 ((1 / (8 * Real.pi * (CM8.euclidNorm y) ^ 3)) • normSq3_CLM' y) y := by
-- proof
  have h := (hasDerivAt_neg_inv_4pi_sqrt (normSq3' y) (normSq3_pos' y hy)).comp_hasFDerivAt
    y (hasFDerivAt_normSq3' y)
  convert h using 1

end PoissonHarnack

namespace PoissonHarnack

/--
[hasFDerivAt_const_sub_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma hasFDerivAt_const_sub_fin3
  {a y : Fin 3 → ℝ} :
-- imply
  HasFDerivAt (fun y' : Fin 3 → ℝ => a - y') (-(ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) y := by
-- proof
  have h1 : HasFDerivAt (fun _ : Fin 3 → ℝ => a) (0 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) y :=
    hasFDerivAt_const a y
  have h2 : HasFDerivAt (fun y' : Fin 3 → ℝ => y') (ContinuousLinearMap.id ℝ (Fin 3 → ℝ)) y :=
    hasFDerivAt_id y
  convert h1.sub h2 using 1; ext v; simp

end PoissonHarnack

namespace PoissonHarnack

/--
[hasFDerivAt_Phi3_sub_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma hasFDerivAt_Phi3_sub_chain
  {a y : Fin 3 → ℝ}
-- given
  (ha : CM8.euclidNorm (a - y) ≠ 0) :
-- imply
  HasFDerivAt (fun y' => CM8.Phi3 (a - y')) (((1 / (8 * Real.pi * (CM8.euclidNorm (a - y)) ^ 3)) • normSq3_CLM' (a - y)).comp (-(ContinuousLinearMap.id ℝ (Fin 3 → ℝ)))) y :=
-- proof
  (hasFDerivAt_Phi3_direct (a - y) ha).comp y (hasFDerivAt_const_sub_fin3 a y)

end PoissonHarnack

namespace PoissonHarnack

/--
[normSq3_CLM_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma normSq3_CLM_apply'
  {x v : Fin 3 → ℝ} :
-- imply
  normSq3_CLM' x v = ∑ j : Fin 3, 2 * x j * v j := by
-- proof
  unfold normSq3_CLM'
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]

end PoissonHarnack

namespace PoissonHarnack

/--
[fderiv_Phi3_sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma fderiv_Phi3_sub_eq
  {a y : Fin 3 → ℝ}
  {v : Fin 3 → ℝ}
-- given
  (ha : CM8.euclidNorm (a - y) ≠ 0) :
-- imply
  fderiv ℝ (fun y' => CM8.Phi3 (a - y')) y v = -((∑ i : Fin 3, (a i - y i) * v i) / (4 * Real.pi * CM8.euclidNorm (a - y) ^ 3)) := by
-- proof
  rw [(hasFDerivAt_Phi3_sub_chain a y ha).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  rw [normSq3_CLM_apply']
  simp only [Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  have h1 : (∑ j : Fin 3, 2 * (a j - y j) * -v j) =
    -2 * (∑ j : Fin 3, (a j - y j) * v j) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [h1]; ring

end PoissonHarnack

namespace PoissonHarnack

/--
[differentiableAt_Phi3_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma differentiableAt_Phi3_sub
  {a y : Fin 3 → ℝ}
-- given
  (ha : CM8.euclidNorm (a - y) ≠ 0) :
-- imply
  DifferentiableAt ℝ (fun y' => CM8.Phi3 (a - y')) y :=
-- proof
  (hasFDerivAt_Phi3_sub_chain a y ha).differentiableAt

end PoissonHarnack

namespace PoissonHarnack

/--
[fderiv_greenBall_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma fderiv_greenBall_decompose
  {R : ℝ}
  {p x : Fin 3 → ℝ}
  {σ : Fin 3 → ℝ}
  {v : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hx : CM8.euclidNorm (x - p) < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  fderiv ℝ (fun y => greenBall R p x y) σ v = fderiv ℝ (fun y => CM8.Phi3 (x - y)) σ v - (R / CM8.euclidNorm (x - p)) * fderiv ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ v := by
-- proof
  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith
  have h_norm := norm_product_identity p x σ R hR hxp hσ
  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith
  have hd1 : DifferentiableAt ℝ (fun y => CM8.Phi3 (x - y)) σ :=
    differentiableAt_Phi3_sub x σ hxs_ne
  have hd2 : DifferentiableAt ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    differentiableAt_Phi3_sub (kelvinReflection p R x) σ hkr_ne
  have hfg : (fun y => greenBall R p x y) =
    (fun y => CM8.Phi3 (x - y) - R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) := by
    ext y; simp [greenBall]
  rw [hfg]
  have hcg : DifferentiableAt ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    hd2.const_mul _
  have key : fderiv ℝ (fun y => CM8.Phi3 (x - y) - R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ =
    fderiv ℝ (fun y => CM8.Phi3 (x - y)) σ - fderiv ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    (hd1.hasFDerivAt.sub hcg.hasFDerivAt).fderiv
  rw [key]
  simp only [ContinuousLinearMap.sub_apply]
  congr 1
  have hconst : fderiv ℝ (fun y => R / CM8.euclidNorm (x - p) * CM8.Phi3 (kelvinReflection p R x - y)) σ =
    (R / CM8.euclidNorm (x - p)) • fderiv ℝ (fun y => CM8.Phi3 (kelvinReflection p R x - y)) σ :=
    (hd2.hasFDerivAt.const_mul _).fderiv
  rw [hconst, ContinuousLinearMap.smul_apply, smul_eq_mul]

end PoissonHarnack

namespace PoissonHarnack

/--
[fderiv_greenBall_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma fderiv_greenBall_eq
  {R : ℝ}
  {p x : Fin 3 → ℝ}
  {σ : Fin 3 → ℝ}
  {v : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hx : CM8.euclidNorm (x - p) < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  fderiv ℝ (fun y => greenBall R p x y) σ v = (1 - CM8.euclidNorm (x - p) ^ 2 / R ^ 2) / (4 * Real.pi * CM8.euclidNorm (x - σ) ^ 3) * (∑ i : Fin 3, (σ i - p i) * v i) := by
-- proof
  rw [fderiv_greenBall_decompose R hR p x hx hxp σ hσ v]
  have hd_ne : CM8.euclidNorm (x - p) ≠ 0 := ne_of_gt hxp
  have hxs_ne : CM8.euclidNorm (x - σ) ≠ 0 := by
    intro h
    have heq := euclidNorm_zero_imp_eq x σ h
    subst heq; linarith
  have h_norm := norm_product_identity p x σ R hR hxp hσ
  have hkr_ne : CM8.euclidNorm (kelvinReflection p R x - σ) ≠ 0 := by
    intro h; rw [h, zero_mul] at h_norm
    have : 0 < R * CM8.euclidNorm (x - σ) :=
      mul_pos hR (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne))
    linarith
  rw [fderiv_Phi3_sub_eq x σ hxs_ne v]
  rw [fderiv_Phi3_sub_eq (kelvinReflection p R x) σ hkr_ne v]
  set d := CM8.euclidNorm (x - p) with hd_def
  set e := CM8.euclidNorm (x - σ) with he_def
  set k := CM8.euclidNorm (kelvinReflection p R x - σ) with hk_def
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have he_pos : 0 < e := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hxs_ne)
  have hk_pos : 0 < k := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hkr_ne)
  have h_kr_comp : ∀ i : Fin 3,
    kelvinReflection p R x i - σ i = R ^ 2 / d ^ 2 * (x i - p i) - (σ i - p i) := by
    intro i; simp [kelvinReflection]; ring
  have h_kr_sum : (∑ i : Fin 3, (kelvinReflection p R x i - σ i) * v i) =
    R ^ 2 / d ^ 2 * (∑ i : Fin 3, (x i - p i) * v i) - ∑ i : Fin 3, (σ i - p i) * v i := by
    simp_rw [h_kr_comp]; simp only [Fin.sum_univ_three]; ring
  have h_xs_sum : (∑ i : Fin 3, (x i - σ i) * v i) =
    (∑ i : Fin 3, (x i - p i) * v i) - ∑ i : Fin 3, (σ i - p i) * v i := by
    simp only [Fin.sum_univ_three]; ring
  rw [h_kr_sum, h_xs_sum]
  set Sxp := ∑ i : Fin 3, (x i - p i) * v i with hSxp_def
  set Ssp := ∑ i : Fin 3, (σ i - p i) * v i with hSsp_def
  have hk_eq : k = R * e / d := by
    field_simp; linarith [h_norm]
  have hk3_eq : k ^ 3 = R ^ 3 * e ^ 3 / d ^ 3 := by
    rw [hk_eq]; field_simp
  rw [hk3_eq]
  have he_ne : e ≠ 0 := ne_of_gt he_pos
  have h4pie3 : (4 : ℝ) * π * e ^ 3 ≠ 0 := by positivity
  field_simp
  ring

end PoissonHarnack

namespace PoissonHarnack

/--
[greenBall_normal_deriv_eq_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma greenBall_normal_deriv_eq_poisson
  {R : ℝ}
  {p x : Fin 3 → ℝ}
  {σ : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hx : CM8.euclidNorm (x - p) < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  CM8.normalDeriv {y | CM8.euclidNorm (y - p) < R} (fun y => greenBall R p x y) σ = poissonKernel R p x σ := by
-- proof
  unfold CM8.normalDeriv
  rw [outwardUnitNormal_euclidBall R hR p σ hσ]
  rw [fderiv_greenBall_eq R hR p x hx hxp σ hσ]
  unfold poissonKernel
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hR2_ne : R ^ 2 ≠ 0 := pow_ne_zero 2 hR_ne
  have h_inner : (∑ i : Fin 3, (σ i - p i) * ((σ i - p i) / R)) =
    CM8.euclidNorm (σ - p) ^ 2 / R := by
    unfold CM8.euclidNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    have : ∀ i : Fin 3, (σ i - p i) * ((σ i - p i) / R) = (σ - p) i ^ 2 / R := by
      intro i; simp [Pi.sub_apply]; field_simp
    simp_rw [this, Finset.sum_div]
  rw [h_inner, hσ]
  field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[lemma_2_0_1_green_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma lemma_2_0_1_green_ball
  {R : ℝ}
  {p x : Fin 3 → ℝ}
  {σ : Fin 3 → ℝ}
-- given
  (hR : 0 < R)
  (hx : CM8.euclidNorm (x - p) < R)
  (hxp : 0 < CM8.euclidNorm (x - p))
  (hσ : CM8.euclidNorm (σ - p) = R) :
-- imply
  (greenBall R p x σ = greenBallFormula R p x σ) ∧ (greenBall R p x σ = 0) ∧ (Filter.Tendsto (fun z => greenBall R p z σ) (nhdsWithin p {z | 0 < CM8.euclidNorm (z - p)}) (nhds (greenBallFormula_at_center R p σ))) ∧ (CM8.normalDeriv {y | CM8.euclidNorm (y - p) < R} (fun y => greenBall R p x y) σ = poissonKernel R p x σ) :=
-- proof
  ⟨greenBall_eq_explicit_formula R p x σ,
    greenBall_boundary_vanish R hR p x σ hxp hx hσ,
    greenBall_at_center_eq_formula R hR p σ hσ,
    greenBall_normal_deriv_eq_poisson R hR p x hx hxp σ hσ⟩

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_eq_piLp_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_eq_piLp_norm
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  CM8.euclidNorm v = ‖toPiLp v‖ := by
-- proof
  unfold CM8.euclidNorm toPiLp
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [WithLp.equiv, Real.norm_eq_abs, sq_abs]

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_sub_le
  {n : ℕ}
  {a b : Fin n → ℝ} :
-- imply
  CM8.euclidNorm (a - b) ≤ CM8.euclidNorm a + CM8.euclidNorm b := by
-- proof
  rw [euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm]
  have h : toPiLp (a - b) = toPiLp a - toPiLp b := by
    unfold toPiLp; simp [WithLp.equiv]
  rw [h]; exact norm_sub_le (toPiLp a) (toPiLp b)

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_reverse_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_reverse_triangle
  {n : ℕ}
  {x σ : Fin n → ℝ} :
-- imply
  CM8.euclidNorm σ - CM8.euclidNorm x ≤ CM8.euclidNorm (x - σ) := by
-- proof
  rw [euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm, euclidNorm_eq_piLp_norm]
  have h : toPiLp (x - σ) = toPiLp x - toPiLp σ := by
    unfold toPiLp; simp [WithLp.equiv]
  rw [h]
  have := abs_le.mp (abs_norm_sub_norm_le (toPiLp x) (toPiLp σ))
  linarith [this.2]

end PoissonHarnack

namespace PoissonHarnack

/--
[distance_upper_bound_on_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma distance_upper_bound_on_sphere
  {n : ℕ}
  {x σ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hσ : CM8.euclidNorm σ = R) :
-- imply
  CM8.euclidNorm (x - σ) ≤ R + CM8.euclidNorm x := by
-- proof
  calc CM8.euclidNorm (x - σ)
    ≤ CM8.euclidNorm x + CM8.euclidNorm σ := euclidNorm_sub_le x σ
    _ = CM8.euclidNorm x + R := by rw [hσ]
    _ = R + CM8.euclidNorm x := by ring

end PoissonHarnack

namespace PoissonHarnack

/--
[distance_lower_bound_on_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma distance_lower_bound_on_sphere
  {n : ℕ}
  {x σ : Fin n → ℝ}
  {R : ℝ}
-- given
  (hσ : CM8.euclidNorm σ = R) :
-- imply
  R - CM8.euclidNorm x ≤ CM8.euclidNorm (x - σ) := by
-- proof
  calc R - CM8.euclidNorm x = CM8.euclidNorm σ - CM8.euclidNorm x := by rw [hσ]
    _ ≤ CM8.euclidNorm (x - σ) := euclidNorm_reverse_triangle x σ

end PoissonHarnack

namespace PoissonHarnack

/--
[poisson_representation_weight_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma poisson_representation_weight_axiom
  {n : ℕ}
  {u : (Fin n → ℝ) → ℝ}
  {R : ℝ}
  {x : Fin n → ℝ}
-- given
  (hR : 0 < R)
  (_hu_harmonic : CM7.IsHarmonic u (euclidBall 0 R))
  (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin n → ℝ) R, 0 ≤ u x)
  (hx : x ∈ euclidBall (0 : Fin n → ℝ) R) :
-- imply
  ∃ W : ℝ, 0 ≤ W ∧ u x = (R ^ 2 - CM8.euclidNorm x ^ 2) * W := by
-- proof
  have hx_mem : CM8.euclidNorm (x - 0) < R := hx
  simp only [sub_zero] at hx_mem
  have hNorm_nonneg : 0 ≤ CM8.euclidNorm x := by
    unfold CM8.euclidNorm; exact Real.sqrt_nonneg _
  have hR2_pos : R ^ 2 - CM8.euclidNorm x ^ 2 > 0 := by
    have : CM8.euclidNorm x ^ 2 < R ^ 2 := by
      apply sq_lt_sq'
      · linarith
      · exact hx_mem
    linarith
  refine ⟨u x / (R ^ 2 - CM8.euclidNorm x ^ 2), ?_, ?_⟩
  · exact div_nonneg (hu_nonneg x hx) (le_of_lt hR2_pos)
  · field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[lower_bound_simplify](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma lower_bound_simplify
  {R d a : ℝ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hRd : R + d ≠ 0) :
-- imply
  R ^ (n - 2) * (R ^ 2 - d ^ 2) / (R + d) ^ n * a = R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a := by
-- proof
  have h1 : R ^ 2 - d ^ 2 = (R - d) * (R + d) := by ring
  rw [h1, show (R + d) ^ n = (R + d) ^ (n - 1) * (R + d) from by
    rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega)]]
  field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[upper_bound_simplify](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma upper_bound_simplify
  {R d a : ℝ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hRd : R - d ≠ 0) :
-- imply
  R ^ (n - 2) * (R ^ 2 - d ^ 2) / (R - d) ^ n * a = R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a := by
-- proof
  have h1 : R ^ 2 - d ^ 2 = (R + d) * (R - d) := by ring
  rw [h1, show (R - d) ^ n = (R - d) ^ (n - 1) * (R - d) from by
    rw [← pow_succ, Nat.sub_one_add_one_eq_of_pos (by omega)]]
  field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_fin_zero
  {x : Fin 0 → ℝ} :
-- imply
  CM8.euclidNorm x = 0 := by
-- proof
  unfold CM8.euclidNorm
  simp [Finset.sum_empty]

end PoissonHarnack

namespace PoissonHarnack

/--
[lower_bound_n_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma lower_bound_n_zero
  {u : (Fin 0 → ℝ) → ℝ}
  {R : ℝ}
  {x : Fin 0 → ℝ}
-- given
  (hR : 0 < R)
  (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin 0 → ℝ) R, 0 ≤ u x)
  (_hx : x ∈ euclidBall (0 : Fin 0 → ℝ) R)
  (h : (R ^ 2 - CM8.euclidNorm x ^ 2) * u 0 ≤ u x) :
-- imply
  (R - CM8.euclidNorm x) * u 0 ≤ u x := by
-- proof
  rw [euclidNorm_fin_zero x] at h ⊢
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero] at h ⊢
  have hx0 : x = 0 := by ext i; exact i.elim0
  rw [hx0] at h ⊢
  have hu0 : 0 ≤ u 0 := hu_nonneg 0 (by simp [euclidBall, CM8.euclidNorm]; exact hR)
  nlinarith [sq_nonneg (R - 1)]

end PoissonHarnack

namespace PoissonHarnack

/--
[upper_bound_n_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma upper_bound_n_zero
  {u : (Fin 0 → ℝ) → ℝ}
  {R : ℝ}
  {x : Fin 0 → ℝ}
-- given
  (hR : 0 < R)
  (hu_nonneg : ∀ x ∈ euclidBall (0 : Fin 0 → ℝ) R, 0 ≤ u x)
  (_hx : x ∈ euclidBall (0 : Fin 0 → ℝ) R)
  (h : u x ≤ (R ^ 2 - CM8.euclidNorm x ^ 2) * u 0) :
-- imply
  u x ≤ (R + CM8.euclidNorm x) * u 0 := by
-- proof
  rw [euclidNorm_fin_zero x] at h ⊢
  simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero, add_zero] at h ⊢
  have hx0 : x = 0 := by ext i; exact i.elim0
  rw [hx0] at h ⊢
  have hu0 : 0 ≤ u 0 := hu_nonneg 0 (by simp [euclidBall, CM8.euclidNorm]; exact hR)
  nlinarith [sq_nonneg (R - 1)]

end PoissonHarnack

namespace PoissonHarnack

/--
[euclidNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma euclidNorm_nonneg
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  0 ≤ CM8.euclidNorm v :=
-- proof
  Real.sqrt_nonneg _

end PoissonHarnack

namespace PoissonHarnack

/--
[laplacian_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma laplacian_const
  {n : ℕ}
  {c : ℝ} :
-- imply
  CM7.Laplacian n (fun _ : Fin n → ℝ => c) = fun _ => 0 :=
-- proof
  CM7.laplacian_const c

end PoissonHarnack

namespace PoissonHarnack

/--
[isHarmonic_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma isHarmonic_const
  {n : ℕ}
  {c : ℝ}
  {Ω : Set (Fin n → ℝ)} :
-- imply
  CM7.IsHarmonic (fun _ => c) Ω where contDiffOn :=
-- proof
  contDiff_const.contDiffOn
    laplacian_eq_zero := by
      intro x _
      have h := congr_fun (laplacian_const (n := n) c) x
      exact h

end PoissonHarnack

namespace PoissonHarnack

/--
[IsHarmonic.add_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma IsHarmonic.add_const
  {n : ℕ}
  {u : (Fin n → ℝ) → ℝ}
  {Ω : Set (Fin n → ℝ)}
  {c : ℝ}
-- given
  (hu : CM7.IsHarmonic u Ω)
  (hΩ : IsOpen Ω) :
-- imply
  CM7.IsHarmonic (fun x => u x + c) Ω := by
-- proof
  have heq : (fun x => u x + c) = (fun x => u x - (fun _ => -c) x) := by
    ext x; ring
  rw [heq]
  exact hu.sub hΩ (isHarmonic_const (-c) Ω)

end PoissonHarnack

namespace PoissonHarnack

/--
[IsHarmonic.restrict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma IsHarmonic.restrict
  {n : ℕ}
  {u : (Fin n → ℝ) → ℝ}
  {Ω : Set (Fin n → ℝ)}
-- given
  (hu : CM7.IsHarmonic u Set.univ) :
-- imply
  CM7.IsHarmonic u Ω where contDiffOn :=
-- proof
  hu.contDiffOn.mono (Set.subset_univ _)
    laplacian_eq_zero := by
      intro x _
      exact hu.laplacian_eq_zero x (Set.mem_univ x)

end PoissonHarnack

namespace PoissonHarnack

/--
[mem_euclidBall_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma mem_euclidBall_of_lt
  {n : ℕ}
  {x : Fin n → ℝ}
  {R : ℝ}
-- given
  (hR : CM8.euclidNorm x < R) :
-- imply
  x ∈ euclidBall (0 : Fin n → ℝ) R := by
-- proof
  show CM8.euclidNorm (x - 0) < R
  simp [sub_zero]
  exact hR

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_div_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_div_sub_const
  {d : ℝ} :
-- imply
  Tendsto (fun R : ℝ => R / (R - d)) atTop (nhds 1) := by
-- proof
  suffices h : Tendsto (fun R : ℝ => 1 + d / (R - d)) atTop (nhds (1 + 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop d] with R hR
    have hRd : R - d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_add
  apply Tendsto.div_atTop tendsto_const_nhds
  exact (tendsto_atTop_add_const_right atTop (-d) tendsto_id)

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_pow_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_pow_ratio
  {k : ℕ}
  {d : ℝ} :
-- imply
  Tendsto (fun R : ℝ => R ^ k / (R - d) ^ k) atTop (nhds 1) := by
-- proof
  rw [show (fun R : ℝ => R ^ k / (R - d) ^ k) = (fun R => (R / (R - d)) ^ k) from
    by ext R; rw [div_pow], show (1 : ℝ) = 1 ^ k from (one_pow k).symm]
  exact (tendsto_div_sub_const d).pow k

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_add_div_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_add_div_sub
  {d : ℝ} :
-- imply
  Tendsto (fun R : ℝ => (R + d) / (R - d)) atTop (nhds 1) := by
-- proof
  suffices h : Tendsto (fun R : ℝ => 1 + 2 * d / (R - d)) atTop (nhds (1 + 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop d] with R hR
    have hRd : R - d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_add
  apply Tendsto.div_atTop tendsto_const_nhds
  exact (tendsto_atTop_add_const_right atTop (-d) tendsto_id)

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_sub_div_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_sub_div_add
  {d : ℝ}
-- given
  (hd : 0 ≤ d) :
-- imply
  Tendsto (fun R : ℝ => (R - d) / (R + d)) atTop (nhds 1) := by
-- proof
  suffices h : Tendsto (fun R : ℝ => 1 - 2 * d / (R + d)) atTop (nhds (1 - 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRd : R + d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_sub
  apply Tendsto.div_atTop tendsto_const_nhds
  exact tendsto_atTop_add_const_right atTop d tendsto_id

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_div_add_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_div_add_const
  {d : ℝ}
-- given
  (hd : 0 ≤ d) :
-- imply
  Tendsto (fun R : ℝ => R / (R + d)) atTop (nhds 1) := by
-- proof
  suffices h : Tendsto (fun R : ℝ => 1 - d / (R + d)) atTop (nhds (1 - 0)) by
    simp at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    have hRd : R + d ≠ 0 := by linarith
    field_simp
    ring
  apply Tendsto.const_sub
  apply Tendsto.div_atTop tendsto_const_nhds
  exact tendsto_atTop_add_const_right atTop d tendsto_id

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_pow_ratio_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_pow_ratio_add
  {k : ℕ}
  {d : ℝ}
-- given
  (hd : 0 ≤ d) :
-- imply
  Tendsto (fun R : ℝ => R ^ k / (R + d) ^ k) atTop (nhds 1) := by
-- proof
  rw [show (fun R : ℝ => R ^ k / (R + d) ^ k) = (fun R => (R / (R + d)) ^ k) from
    by ext R; rw [div_pow], show (1 : ℝ) = 1 ^ k from (one_pow k).symm]
  exact (tendsto_div_add_const d hd).pow k

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_upper_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_upper_coeff
  {n : ℕ}
  {d : ℝ}
-- given
  (hn : 2 ≤ n) :
-- imply
  Tendsto (fun R : ℝ => R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1)) atTop (nhds 1) := by
-- proof
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm]
  refine Tendsto.congr ?_ ((tendsto_pow_ratio (n - 2) d).mul (tendsto_add_div_sub d))
  intro R
  simp only [hn1, pow_succ]
  by_cases hRd : R - d = 0
  · simp [hRd]
  · field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[tendsto_lower_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma tendsto_lower_coeff
  {n : ℕ}
  {d : ℝ}
-- given
  (hn : 2 ≤ n)
  (hd : 0 ≤ d) :
-- imply
  Tendsto (fun R : ℝ => R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1)) atTop (nhds 1) := by
-- proof
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  rw [show (1 : ℝ) = 1 * 1 from (mul_one 1).symm]
  refine Tendsto.congr ?_ ((tendsto_pow_ratio_add (n - 2) d hd).mul (tendsto_sub_div_add d hd))
  intro R
  simp only [hn1, pow_succ]
  by_cases hRd : R + d = 0
  · simp [hRd]
  · field_simp

end PoissonHarnack

namespace PoissonHarnack

/--
[harnack_upper_squeeze](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/PoissonHarnackLiouville.lean)
-/
@[path]
lemma harnack_upper_squeeze
  {n : ℕ}
  {d : ℝ}
  {a b : ℝ}
-- given
  (hd : 0 ≤ d)
  (h_le : ∀ R : ℝ, d < R → b ≤ R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a)
  (h_ge : ∀ R : ℝ, d < R → R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a ≤ b) :
-- imply
  b = a := by
-- proof
  obtain hn | hn := Nat.lt_or_ge n 2
  ·
    have hn2 : n - 2 = 0 := by omega
    have hn1 : n - 1 = 0 := by omega
    simp only [hn2, hn1, pow_zero, one_mul, div_one] at h_le h_ge
    have ha : a = 0 := by
      by_contra ha_ne
      obtain ha_neg | ha_pos := lt_or_gt_of_ne ha_ne
      ·
        have hna : (0 : ℝ) < -a := neg_pos.mpr ha_neg
        have hab : (0 : ℝ) < (|b| + 1) / (-a) := div_pos (by positivity) hna
        have hR : d < d + (|b| + 1) / (-a) + 1 := by linarith
        have h := h_le (d + (|b| + 1) / (-a) + 1) hR
        have hineq : (d + (|b| + 1) / (-a) + 1 + d) * a ≤ ((|b| + 1) / (-a) + 1) * a := by
          nlinarith [mul_le_mul_of_nonpos_right
            (show d + (|b| + 1) / (-a) + 1 + d ≥ (|b| + 1) / (-a) + 1 from by linarith)
            (le_of_lt ha_neg)]
        have hval : ((|b| + 1) / (-a) + 1) * a = -(|b| + 1) + a := by
          field_simp
        linarith [neg_abs_le b]
      ·
        have hab : (0 : ℝ) < (|b| + 1) / a := div_pos (by positivity) ha_pos
        have hR : d < d + (|b| + 1) / a + 1 := by linarith
        have h := h_ge (d + (|b| + 1) / a + 1) hR
        have hsimp : (d + (|b| + 1) / a + 1 - d) * a = |b| + 1 + a := by
          field_simp; ring
        linarith [le_abs_self b]
    subst ha
    have h1 := h_ge (d + 1) (by linarith)
    have h2 := h_le (d + 1) (by linarith)
    linarith
  ·
    apply le_antisymm
    ·
      have hlim : Tendsto (fun R => R ^ (n - 2) * (R + d) / (R - d) ^ (n - 1) * a)
        atTop (nhds (1 * a)) :=
        (tendsto_upper_coeff n hn d).mul tendsto_const_nhds
      simp only [one_mul] at hlim
      exact ge_of_tendsto hlim
        (eventually_atTop.mpr ⟨d + 1, fun R hR => h_le R (by linarith)⟩)
    ·
      have hlim : Tendsto (fun R => R ^ (n - 2) * (R - d) / (R + d) ^ (n - 1) * a)
        atTop (nhds (1 * a)) :=
        (tendsto_lower_coeff n hn d hd).mul tendsto_const_nhds
      simp only [one_mul] at hlim
      exact le_of_tendsto hlim
        (eventually_atTop.mpr ⟨d + 1, fun R hR => h_ge R (by linarith)⟩)
/-- Liouville's theorem for non-negative harmonic functions: a non-negative harmonic function
on $\mathbb{R}^n$ is constant. -/

end PoissonHarnack


-- created on 2026-10-23
