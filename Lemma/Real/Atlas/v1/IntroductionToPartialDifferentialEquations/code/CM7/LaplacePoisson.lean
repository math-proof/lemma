import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplacePoisson
open Real Set MeasureTheory Filter LaplacePoisson


namespace LaplacePoisson

/--
[euclidNormLP_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclidNormLP_neg
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  euclidNormLP (-x) = euclidNormLP x := by
-- proof
  unfold euclidNormLP
  congr 1; congr 1; ext i; simp

end LaplacePoisson

namespace LaplacePoisson

/--
[euclidNormLP_eq_norm_withLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclidNormLP_eq_norm_withLp
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  euclidNormLP v = ‖(WithLp.equiv 2 (Fin n → ℝ)).symm v‖ := by
-- proof
  unfold euclidNormLP
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.equiv_symm_apply_ofLp]
  simp [sq_abs]

end LaplacePoisson

namespace LaplacePoisson

/--
[euclidNormLP_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclidNormLP_nonneg
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  euclidNormLP x ≥ 0 := by
-- proof
  unfold euclidNormLP
  exact Real.sqrt_nonneg _

end LaplacePoisson

namespace LaplacePoisson

/--
[euclidNormLP_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclidNormLP_sub_le
  {n : ℕ}
  {a b : Fin n → ℝ} :
-- imply
  euclidNormLP a - euclidNormLP b ≤ euclidNormLP (a - b) := by
-- proof
  rw [euclidNormLP_eq_norm_withLp a, euclidNormLP_eq_norm_withLp b,
    euclidNormLP_eq_norm_withLp (a - b)]
  have h : (WithLp.equiv 2 (Fin n → ℝ)).symm (a - b) =
    (WithLp.equiv 2 (Fin n → ℝ)).symm a - (WithLp.equiv 2 (Fin n → ℝ)).symm b := by
    ext i
    simp
  rw [h]
  exact norm_sub_norm_le _ _

end LaplacePoisson

namespace LaplacePoisson

/--
[unitSphereArea_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma unitSphereArea_pos
-- imply
  ∀ n, unitSphereArea n > 0 := by
-- proof
  intro n
  unfold unitSphereArea
  split
  · norm_num
  · rename_i hn
    apply div_pos
    · apply mul_pos (by norm_num : (2:ℝ) > 0)
      exact Real.rpow_pos_of_pos Real.pi_pos ((n : ℝ) / 2)
    · apply Real.Gamma_pos_of_pos
      apply div_pos
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      · norm_num

end LaplacePoisson

namespace LaplacePoisson

/--
[unitSphereArea_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma unitSphereArea_three
-- imply
  unitSphereArea 3 = 4 * Real.pi := by
-- proof
  unfold unitSphereArea; simp
  have hG32 : Real.Gamma (3 / 2 : ℝ) = (1 / 2) * Real.Gamma (1 / 2) := by
    have h := Real.Gamma_add_one (s := (1:ℝ)/2) (by norm_num)
    linarith
  have hG12 : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hsqrt : Real.sqrt Real.pi = Real.pi ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow Real.pi
  have hpow : Real.pi ^ ((3:ℝ)/2) = Real.pi * Real.pi ^ ((1:ℝ)/2) := by
    rw [show (3:ℝ)/2 = 1 + 1/2 from by ring]
    rw [Real.rpow_add Real.pi_pos]
    rw [Real.rpow_one]
  rw [hG32, hG12, hsqrt, hpow]
  have hpi12_ne : Real.pi ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  field_simp
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[fundamentalSolution_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma fundamentalSolution_neg
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  fundamentalSolution n (-x) = fundamentalSolution n x := by
-- proof
  unfold fundamentalSolution
  rw [euclidNormLP_neg]

end LaplacePoisson

namespace LaplacePoisson

/--
[hasFDerivAt_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma hasFDerivAt_sum_sq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  HasFDerivAt (fun y : Fin n → ℝ => ∑ j : Fin n, y j ^ 2) (∑ j : Fin n, (2 * x j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
-- proof
  have hfderiv : ∀ j ∈ Finset.univ, HasFDerivAt (fun y : Fin n → ℝ => y j ^ 2)
    ((2 * x j) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
    intro j _
    convert (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.pow 2 using 1
    ext v; simp [mul_comm, smul_eq_mul]
  convert HasFDerivAt.sum hfderiv using 1; ext y; simp [Finset.sum_apply]

end LaplacePoisson

namespace LaplacePoisson

/--
[sum_sq_pos_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma sum_sq_pos_of_ne_zero
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  ∑ j : Fin n, x j ^ 2 > 0 := by
-- proof
  have : ∃ i, x i ≠ 0 := by by_contra h; push Not at h; exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2
    ≥ x i ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

end LaplacePoisson

namespace LaplacePoisson

/--
[hasFDerivAt_euclidNormLP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma hasFDerivAt_euclidNormLP
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  HasFDerivAt (euclidNormLP (n := n)) ((1 / (2 * euclidNormLP x)) • (∑ j : Fin n, (2 * x j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j))) x := by
-- proof
  unfold euclidNormLP
  exact (hasFDerivAt_sum_sq x).sqrt (ne_of_gt (sum_sq_pos_of_ne_zero x hx))

end LaplacePoisson

namespace LaplacePoisson

/--
[euclidNormLP_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclidNormLP_pos
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  euclidNormLP x > 0 := by
-- proof
  unfold euclidNormLP
  apply Real.sqrt_pos_of_pos
  have : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2 ≥ x i ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

end LaplacePoisson

namespace LaplacePoisson

/--
[first_partial_eq_near](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma first_partial_eq_near
  {n : ℕ}
  {g : ℝ → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
  (hx : x ≠ 0) :
-- imply
  (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) =ᶠ[nhds x] (fun y => fderiv ℝ g (euclidNormLP y) 1 * (y i / euclidNormLP y)) := by
-- proof
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨{y | y ≠ 0}, isOpen_ne.mem_nhds hx, fun y hy => ?_⟩
  have hr_pos : euclidNormLP y > 0 := euclidNormLP_pos y hy
  have hg_diff : DifferentiableAt ℝ g (euclidNormLP y) :=
    (hg.differentiableOn two_ne_zero).differentiableAt (Ioi_mem_nhds hr_pos)
  have hchain := hg_diff.hasFDerivAt.comp y (hasFDerivAt_euclidNormLP y hy)
  show fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1) = _
  change fderiv ℝ (g ∘ euclidNormLP) y (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  have harg : 1 / (2 * euclidNormLP y) * ∑ x : Fin n, 2 * y x * (if x = i then (1 : ℝ) else 0)
    = y i / euclidNormLP y := by
    simp [Finset.sum_ite_eq', Finset.mem_univ]; field_simp
  rw [harg]
  have : (fderiv ℝ g (euclidNormLP y)) (y i / euclidNormLP y) =
    (y i / euclidNormLP y) * (fderiv ℝ g (euclidNormLP y)) 1 := by
    conv_lhs => rw [show y i / euclidNormLP y = (y i / euclidNormLP y) • (1 : ℝ) from by simp]
    rw [map_smul, smul_eq_mul]
  rw [this, mul_comm]

end LaplacePoisson

namespace LaplacePoisson

/--
[differentiableAt_coord_over_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma differentiableAt_coord_over_norm
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hx : x ≠ 0) :
-- imply
  DifferentiableAt ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x := by
-- proof
  have : (fun y : Fin n → ℝ => y i / euclidNormLP y) = (fun y => y i * (euclidNormLP y)⁻¹) := by
    ext y; rw [div_eq_mul_inv]
  rw [this]
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt).mul
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt.inv (ne_of_gt (euclidNormLP_pos x hx)))

end LaplacePoisson

namespace LaplacePoisson

/--
[fderiv_coord_over_norm_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma fderiv_coord_over_norm_single
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hx : x ≠ 0) :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x (Pi.single i 1) = 1 / euclidNormLP x - x i ^ 2 / euclidNormLP x ^ 3 := by
-- proof
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  have heq : (fun y : Fin n → ℝ => y i / euclidNormLP y) =
    (fun y => y i * (euclidNormLP y)⁻¹) := by ext y; rw [div_eq_mul_inv]
  rw [heq]
  have h1 : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x :=
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt).inv hr_ne
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y i) x (Pi.single i 1) = 1 := by
    have : (fun y : Fin n → ℝ => y i) =
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := rfl
    rw [this, ContinuousLinearMap.fderiv]; simp
  rw [hproj]
  rw [show fderiv ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x =
    fderiv ℝ (Inv.inv ∘ euclidNormLP) x from rfl,
    ((hasFDerivAt_inv' (𝕜 := ℝ) hr_ne).comp x (hasFDerivAt_euclidNormLP x hx)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  field_simp
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[differentiableAt_gprime_comp_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma differentiableAt_gprime_comp_norm
  {n : ℕ}
  {g : ℝ → ℝ}
  {x : Fin n → ℝ}
-- given
  (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
  (hx : x ≠ 0) :
-- imply
  DifferentiableAt ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x := by
-- proof
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ (fun s => fderiv ℝ g s 1) (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  exact (hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))).comp x
    (hasFDerivAt_euclidNormLP x hx).differentiableAt

end LaplacePoisson

namespace LaplacePoisson

/--
[fderiv_gprime_comp_norm_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma fderiv_gprime_comp_norm_single
  {n : ℕ}
  {g : ℝ → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
  (hx : x ≠ 0) :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x (Pi.single i 1) = fderiv ℝ (fun s => fderiv ℝ g s 1) (euclidNormLP x) 1 * (x i / euclidNormLP x) := by
-- proof
  set phi := (fun s : ℝ => fderiv ℝ g s 1) with hphi_def
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ phi (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  have hphi_diffAt : DifferentiableAt ℝ phi (euclidNormLP x) :=
    hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))
  have hchain := hphi_diffAt.hasFDerivAt.comp x (hasFDerivAt_euclidNormLP x hx)
  show fderiv ℝ (fun y => phi (euclidNormLP y)) x (Pi.single i 1) = _
  change fderiv ℝ (phi ∘ euclidNormLP) x (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  field_simp

end LaplacePoisson

namespace LaplacePoisson

/--
[axm_second_partial_comp_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma axm_second_partial_comp_norm
  {n : ℕ}
  {g : ℝ → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
  (hx : x ≠ 0) :
-- imply
  let r := euclidNormLP x fderiv ℝ (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) x (Pi.single i 1) = fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 * (x i / r) ^ 2 + fderiv ℝ g r 1 * (1 / r - x i ^ 2 / r ^ 3) := by
-- proof
  intro r
  rw [(first_partial_eq_near g hg x hx i).fderiv_eq]
  rw [fderiv_fun_mul (differentiableAt_gprime_comp_norm g hg x hx)
    (differentiableAt_coord_over_norm x hx i)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_gprime_comp_norm_single g hg x hx i,
    fderiv_coord_over_norm_single x hx i]
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[continuous_euclidNormLP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma continuous_euclidNormLP
  {n : ℕ} :
-- imply
  Continuous (fun x : Fin n → ℝ => euclidNormLP x) := by
-- proof
  unfold euclidNormLP
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)

end LaplacePoisson

namespace LaplacePoisson

/--
[norm_sum_div_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma norm_sum_div_sq
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  ∑ i : Fin n, (x i / euclidNormLP x) ^ 2 = 1 := by
-- proof
  have hr := euclidNormLP_pos x hx
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt hr
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have : ∑ i : Fin n, x i ^ 2 = (euclidNormLP x) ^ 2 := by
    unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [this, div_self (pow_ne_zero 2 hr_ne)]

end LaplacePoisson

namespace LaplacePoisson

/--
[spherical_laplacian_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma spherical_laplacian_identity
  {n : ℕ}
  {g : ℝ → ℝ}
  {x : Fin n → ℝ}
-- given
  (hn : n ≥ 2)
  (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
  (hx : x ≠ 0) :
-- imply
  let r := euclidNormLP x laplacianLP (fun y => g (euclidNormLP y)) x = fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 + (↑(n - 1) / r) * fderiv ℝ g r 1 := by
-- proof
  simp only
  set r := euclidNormLP x with hr_def
  have hr := euclidNormLP_pos x hx
  have hr_ne : r ≠ 0 := ne_of_gt hr
  unfold laplacianLP
  simp_rw [axm_second_partial_comp_norm g hg x hx]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, norm_sum_div_sq x hx, mul_one]
  rw [← Finset.mul_sum]
  suffices h : ∑ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = ↑(n - 1) / r by
    rw [h]; ring
  have h1 : ∀ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = (r ^ 2 - x i ^ 2) / r ^ 3 := by
    intro i; field_simp
  simp_rw [h1]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hr2 : ∑ i : Fin n, x i ^ 2 = r ^ 2 := by
    rw [hr_def]; unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [hr2]
  have h_cast : (↑(n - 1) : ℝ) = ↑n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_cast
  rw [h_cast]
  field_simp

end LaplacePoisson

namespace LaplacePoisson

/--
[radial_fundamental_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma radial_fundamental_smooth
  {n : ℕ}
-- given
  (_hn : n ≥ 3) :
-- imply
  ContDiffOn ℝ 2 (fun r : ℝ => -1 / (unitSphereArea n * r ^ (n - 2))) (Set.Ioi 0) := by
-- proof
  set k := n - 2
  set ω := unitSphereArea n
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hfun_eq : (fun r : ℝ => -1 / (ω * r ^ k)) = (fun r => (-1 / ω) * (r ^ k)⁻¹) := by
    funext r; field_simp
  rw [hfun_eq]
  exact (ContDiffOn.inv (contDiff_id.pow k).contDiffOn
    (fun x hx => pow_ne_zero k (ne_of_gt hx))).const_smul (-1 / ω)

end LaplacePoisson

namespace LaplacePoisson

/--
[power_radial_first_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma power_radial_first_deriv
  {n : ℕ}
  {r : ℝ}
-- given
  (hn : n ≥ 3)
  (hr : r > 0) :
-- imply
  fderiv ℝ (fun s : ℝ => -1 / (unitSphereArea n * s ^ (n - 2))) r 1 = (↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1)) := by
-- proof
  rw [fderiv_apply_one_eq_deriv]
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) r (Or.inl hr_ne)).const_mul (-1/ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring, zpow_neg,
    show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring,
    zpow_natCast, hk1]
  field_simp

end LaplacePoisson

namespace LaplacePoisson

/--
[power_radial_second_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma power_radial_second_deriv
  {n : ℕ}
  {r : ℝ}
-- given
  (hn : n ≥ 3)
  (hr : r > 0) :
-- imply
  fderiv ℝ (fun s => fderiv ℝ (fun t : ℝ => -1 / (unitSphereArea n * t ^ (n - 2))) s 1) r 1 = -(↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * r ^ n) := by
-- proof
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hk2 : k + 2 = n := by omega
  have heq : (fun s => fderiv ℝ (fun t : ℝ => -1 / (ω * t ^ k)) s 1) =
    (fun s => deriv (fun t : ℝ => -1 / (ω * t ^ k)) s) := by
    ext s; exact fderiv_apply_one_eq_deriv
  rw [heq, fderiv_apply_one_eq_deriv]
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  have hderiv_eq : ∀ᶠ s in nhds r, deriv (fun t : ℝ => -1 / (ω * t ^ k)) s =
    (↑k / ω) * s ^ (-((k : ℤ) + 1)) := by
    filter_upwards [eventually_gt_nhds (by linarith : (0 : ℝ) < r)] with s hs
    rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) s (Or.inl (ne_of_gt hs))).const_mul (-1/ω) |>.deriv]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring]
    field_simp
  rw [Filter.EventuallyEq.deriv_eq hderiv_eq,
    (hasDerivAt_zpow (-((k : ℤ) + 1)) r (Or.inl hr_ne)).const_mul (↑k / ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [show -((k : ℤ) + 1) - 1 = -(((k : ℤ) + 1) + 1) from by ring, zpow_neg,
    show ((k : ℤ) + 1) + 1 = ((k + 2 : ℕ) : ℤ) from by push_cast; ring,
    zpow_natCast, hk2]
  have : (k : ℝ) + 1 = ↑(n - 1) := by rw [← hk1]; push_cast; ring
  rw [this]; field_simp

end LaplacePoisson

namespace LaplacePoisson

/--
[fundamental_solution_harmonic_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma fundamental_solution_harmonic_away
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hn : n ≥ 3)
  (hx : x ≠ 0) :
-- imply
  laplacianLP (fundamentalSolution n) x = 0 := by
-- proof
  have hn2 : n ≠ 2 := by omega
  let g : ℝ → ℝ := fun s => -1 / (unitSphereArea n * s ^ (n - 2))
  have hfg : fundamentalSolution n = fun y => g (euclidNormLP y) := by
    ext y; simp only [fundamentalSolution, hn2, ite_false, g]
  rw [hfg]
  have hn2' : n ≥ 2 := by omega
  have hg_smooth := radial_fundamental_smooth n hn
  rw [spherical_laplacian_identity hn2' g hg_smooth x hx]
  have hr := euclidNormLP_pos x hx
  rw [power_radial_second_deriv n hn (euclidNormLP x) hr,
    power_radial_first_deriv n hn (euclidNormLP x) hr]
  set r := euclidNormLP x
  have h1 : r * r ^ (n - 1) = r ^ n := by
    calc r * r ^ (n - 1) = r ^ 1 * r ^ (n - 1) := by ring
      _ = r ^ (1 + (n - 1)) := by rw [pow_add]
      _ = r ^ n := by congr 1; omega
  have key : (↑(n - 1) : ℝ) / r * ((↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1))) =
    (↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * (r * r ^ (n - 1))) := by ring
  rw [key, h1]
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[convolution_substitution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma convolution_substitution
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ} :
-- imply
  (∫ y, fundamentalSolution n (x - y) * f y) = ∫ y, fundamentalSolution n y * f (x - y) := by
-- proof
  have key : ∀ y : Fin n → ℝ,
    fundamentalSolution n (x - y) * f y =
    (fun z => fundamentalSolution n z * f (x - z)) (x - y) := by
    intro y; simp [sub_sub_cancel]
  simp_rw [key]
  exact MeasureTheory.integral_sub_left_eq_self
    (fun z : Fin n → ℝ => fundamentalSolution n z * f (x - z))
    (volume : Measure (Fin n → ℝ)) x

end LaplacePoisson

namespace LaplacePoisson

/--
[fderiv_comp_const_sub_LP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma fderiv_comp_const_sub_LP
  {n : ℕ}
  {g : (Fin n → ℝ) → ℝ}
  {x z' : Fin n → ℝ}
-- given
  (hg : DifferentiableAt ℝ g (x - z')) :
-- imply
  fderiv ℝ (fun z => g (x - z)) z' = -(fderiv ℝ g (x - z')) := by
-- proof
  rw [show (fun z => g (x - z)) = g ∘ (fun z => x - z) from rfl,
    fderiv_comp z' hg ((differentiableAt_const x).sub differentiableAt_id)]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  have : fderiv ℝ (fun z : Fin n → ℝ => x - z) z' = -ContinuousLinearMap.id ℝ _ := by
    rw [fderiv_const_sub x]; simp
  rw [this]; simp

end LaplacePoisson

namespace LaplacePoisson

/--
[laplacianLP_chain_rule_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma laplacianLP_chain_rule_sub
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x y : Fin n → ℝ}
-- given
  (_hf : ContDiff ℝ ⊤ f) :
-- imply
  laplacianLP (fun x' => f (x' - y)) x = laplacianLP (fun z => f (x - z)) y := by
-- proof
  suffices h_lhs : laplacianLP (fun x' => f (x' - y)) x = laplacianLP f (x - y) by
    suffices h_rhs : laplacianLP (fun z => f (x - z)) y = laplacianLP f (x - y) by
      rw [h_lhs, h_rhs]
    unfold laplacianLP
    congr 1; ext i
    have hf_diff : ∀ z', DifferentiableAt ℝ f (x - z') :=
      fun z' => (_hf.differentiable WithTop.top_ne_zero).differentiableAt
    have h_func_eq : (fun z' => fderiv ℝ (fun z => f (x - z)) z' (Pi.single i 1))
      = (fun z' => -(fderiv ℝ f (x - z') (Pi.single i 1))) := by
      ext z'; rw [fderiv_comp_const_sub_LP f x z' (hf_diff z')]; simp
    rw [h_func_eq, fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply]
    have hg_diff : DifferentiableAt ℝ (fun w => fderiv ℝ f w (Pi.single i 1)) (x - y) := by
      rw [show (fun w => fderiv ℝ f w (Pi.single i 1)) =
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) ∘ (fderiv ℝ f) from rfl]
      exact DifferentiableAt.comp _
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).differentiableAt
        ((_hf.fderiv_right le_top).differentiable WithTop.top_ne_zero |>.differentiableAt)
    rw [fderiv_comp_const_sub_LP (fun w => fderiv ℝ f w (Pi.single i 1)) x y hg_diff]
    simp
  unfold laplacianLP
  congr 1; ext i
  rw [show (fun z => fderiv ℝ (fun x' => f (x' - y)) z (Pi.single i 1))
    = (fun z => fderiv ℝ f (z - y) (Pi.single i 1)) from by ext z; rw [fderiv_comp_sub y]]
  rw [show (fun z => fderiv ℝ f (z - y) (Pi.single i 1))
    = (fun z => (fun w => fderiv ℝ f w (Pi.single i 1)) (z - y)) from rfl]
  exact @fderiv_comp_sub ℝ _ (Fin n → ℝ) _ _ ℝ _ _
    (fun w => fderiv ℝ f w (Pi.single i 1)) x y ▸ rfl

end LaplacePoisson

namespace LaplacePoisson

/--
[laplacianLP_bounded_of_smooth_compactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma laplacianLP_bounded_of_smooth_compactSupport
  {n : ℕ}
  {g : (Fin n → ℝ) → ℝ}
-- given
  (_hg_smooth : ContDiff ℝ ⊤ g)
  (_hg_supp : HasCompactSupport g) :
-- imply
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Fin n → ℝ, := by
-- proof
  have h_summand_supp : ∀ i : Fin n,
    HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    exact (_hg_supp.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have h_summand_cont : ∀ i : Fin n,
    Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    have h_inner_smooth : ContDiff ℝ ⊤ (fun y => fderiv ℝ g y (Pi.single i 1)) :=
      (_hg_smooth.fderiv_right le_top).clm_apply contDiff_const
    exact (h_inner_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_summand_bound : ∀ i : Fin n, ∃ C : ℝ, ∀ x, ‖(fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1))‖ ≤ C := by
    intro i
    exact (h_summand_supp i).exists_bound_of_continuous (h_summand_cont i)
  choose Cs hCs using h_summand_bound
  refine ⟨∑ i : Fin n, |Cs i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun y => ?_⟩
  unfold laplacianLP
  calc |∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)|
    ≤ ∑ i : Fin n, |fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, |Cs i| := by
      apply Finset.sum_le_sum
      intro i _
      have := hCs i y
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)

end LaplacePoisson

namespace LaplacePoisson

/--
[norm_le_euclidNormLP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma norm_le_euclidNormLP
  {n : ℕ}
  {σ : Fin n → ℝ} :
-- imply
  ‖σ‖ ≤ euclidNormLP σ := by
-- proof
  unfold euclidNormLP
  have h_comp : ∀ i : Fin n, |σ i| ≤ Real.sqrt (∑ j, σ j ^ 2) := by
    intro i
    have h1 : σ i ^ 2 ≤ ∑ j, σ j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (σ j)) (Finset.mem_univ i)
    calc |σ i| = Real.sqrt (σ i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (∑ j, σ j ^ 2) := Real.sqrt_le_sqrt h1
  exact pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr h_comp

end LaplacePoisson

namespace LaplacePoisson

/--
[oscillation_origin_sphere_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma oscillation_origin_sphere_tendsto_zero
  {n : ℕ}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hf : Continuous f) :
-- imply
  Filter.Tendsto (fun ε => ⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}, |f (x - σ) - f x|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hcont := hf.continuousAt (x := x)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη⟩ := hcont (δ / 2) hδ2
  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
  have hfrontier_sub : frontier {z : Fin n → ℝ | euclidNormLP z = ε} ⊆
    {z | euclidNormLP z = ε} := by
    have hclosed : IsClosed {z : Fin n → ℝ | euclidNormLP z = ε} :=
      IsClosed.preimage
        (Continuous.sqrt (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)))
        isClosed_singleton
    exact frontier_subset_closure.trans hclosed.closure_eq.subset
  have hbound : ∀ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
    |f (x - σ) - f x| ≤ δ / 2 := by
    intro σ hσ_frontier
    have hσ_norm : euclidNormLP σ = ε := hfrontier_sub hσ_frontier
    have h_dist : dist (x - σ) x < η := by
      calc dist (x - σ) x = ‖(x - σ) - x‖ := dist_eq_norm _ _
        _ = ‖-σ‖ := by ring_nf
        _ = ‖σ‖ := norm_neg σ
        _ ≤ euclidNormLP σ := norm_le_euclidNormLP σ
        _ = ε := hσ_norm
        _ < η := hε_lt_η
    have h_f_dist := hη h_dist
    rwa [Real.dist_eq] at h_f_dist
  have h_bisup_le : (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
    |f (x - σ) - f x|) ≤ δ / 2 := by
    apply ciSup_le
    intro σ
    by_cases hσ : σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}
    · haveI : Nonempty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) := ⟨hσ⟩
      exact ciSup_le (fun _ => hbound σ hσ)
    · haveI : IsEmpty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) :=
      isEmpty_Prop.mpr hσ
      rwa [Real.iSup_of_isEmpty]
  have h_bisup_nn : 0 ≤ (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
    |f (x - σ) - f x|) := by
    apply Real.sSup_nonneg
    intro y hy
    obtain ⟨σ, rfl⟩ := mem_range.mp hy
    apply Real.sSup_nonneg
    intro z hz
    obtain ⟨_, rfl⟩ := mem_range.mp hz
    exact abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_bisup_nn]
  linarith

end LaplacePoisson

namespace LaplacePoisson

/--
[integral_split_ball_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma integral_split_ball_complement
  {n : ℕ}
  {g : (Fin n → ℝ) → ℝ}
  {ε : ℝ}
-- given
  (_hε : ε > 0)
  (hg : Integrable g) :
-- imply
  ∫ y, g y = (∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, g y) + (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε}, g y) := by
-- proof
  have hms : MeasurableSet {z : Fin n → ℝ | euclidNormLP z < ε} :=
    (isOpen_lt continuous_euclidNormLP continuous_const).measurableSet
  have hcompl : {z : Fin n → ℝ | euclidNormLP z < ε}ᶜ =
    {z : Fin n → ℝ | euclidNormLP z ≥ ε} := by
    ext z; simp [not_lt]
  rw [← hcompl]
  exact (integral_add_compl hms hg).symm

end LaplacePoisson

namespace LaplacePoisson

/--
[eps_sq_abs_log_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma eps_sq_abs_log_tendsto_zero
-- imply
  Filter.Tendsto (fun ε : ℝ => ε ^ 2 * |Real.log ε|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  have h1 := tendsto_log_mul_rpow_nhdsGT_zero (by positivity : (0 : ℝ) < 2)
  rw [tendsto_zero_iff_abs_tendsto_zero] at h1
  refine h1.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro x hx
  rw [Set.mem_Ioi] at hx
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg (rpow_nonneg hx.le 2)]
  rw [show x ^ (2:ℝ) = (x:ℝ) ^ (2:ℕ) from by norm_cast]
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[poisson_solution_unique_nge3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma poisson_solution_unique_nge3
  {n : ℕ}
  {u₁ u₂ : (Fin n → ℝ) → ℝ}
  {f : (Fin n → ℝ) → ℝ}
-- given
  (hn : n ≥ 3)
  (hu₁_smooth : ContDiff ℝ ⊤ u₁)
  (hu₂_smooth : ContDiff ℝ ⊤ u₂)
  (hu₁_pde : ∀ x, laplacianLP u₁ x = f x)
  (hu₂_pde : ∀ x, laplacianLP u₂ x = f x)
  (hu₁_decay : Filter.Tendsto u₁ (Filter.cocompact (Fin n → ℝ)) (nhds 0))
  (hu₂_decay : Filter.Tendsto u₂ (Filter.cocompact (Fin n → ℝ)) (nhds 0)) :
-- imply
  u₁ = u₂ := by
-- proof
  ext x
  suffices h : u₁ x - u₂ x = 0 by linarith
  set w : (Fin n → ℝ) → ℝ := fun y => u₁ y - u₂ y
  have hw_laplacian : ∀ y, laplacianLP w y = 0 := by
    intro y
    have hlin : laplacianLP w y = laplacianLP u₁ y - laplacianLP u₂ y := by
      simp only [laplacianLP, w]
      rw [← Finset.sum_sub_distrib]
      congr 1; ext i
      have heq : (fun z => fderiv ℝ (fun t => u₁ t - u₂ t) z (Pi.single i 1)) =
        (fun z => fderiv ℝ u₁ z (Pi.single i 1) - fderiv ℝ u₂ z (Pi.single i 1)) := by
        ext z
        have hd₁z : DifferentiableAt ℝ u₁ z :=
          hu₁_smooth.contDiffAt.differentiableAt (hn := by simp)
        have hd₂z : DifferentiableAt ℝ u₂ z :=
          hu₂_smooth.contDiffAt.differentiableAt (hn := by simp)
        have h := fderiv_sub hd₁z hd₂z
        simp only [ContinuousLinearMap.sub_apply] at h
        rw [show fderiv ℝ (fun t => u₁ t - u₂ t) z = fderiv ℝ u₁ z - fderiv ℝ u₂ z from
          fderiv_sub hd₁z hd₂z]
        simp [ContinuousLinearMap.sub_apply]
      rw [heq]
      have hd₁' : DifferentiableAt ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1)) y :=
        ((hu₁_smooth.fderiv_right (m := ⊤) le_top).clm_apply contDiff_const).contDiffAt.differentiableAt
          (hn := by simp)
      have hd₂' : DifferentiableAt ℝ (fun z => fderiv ℝ u₂ z (Pi.single i 1)) y :=
        ((hu₂_smooth.fderiv_right (m := ⊤) le_top).clm_apply contDiff_const).contDiffAt.differentiableAt
          (hn := by simp)
      rw [show fderiv ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1) - fderiv ℝ u₂ z (Pi.single i 1)) y =
        fderiv ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1)) y -
        fderiv ℝ (fun z => fderiv ℝ u₂ z (Pi.single i 1)) y from
        fderiv_sub hd₁' hd₂']
      simp [ContinuousLinearMap.sub_apply]
    rw [hlin, hu₁_pde y, hu₂_pde y, sub_self]
  have hw_harmonic : CM7.IsHarmonic w Set.univ :=
    ⟨((hu₁_smooth.sub hu₂_smooth).of_le le_top).contDiffOn, fun y _ => hw_laplacian y⟩
  have hw_smooth2 : ContDiff ℝ 2 w :=
    (hu₁_smooth.sub hu₂_smooth).of_le le_top
  have hw_decay : Filter.Tendsto w (Filter.cocompact (Fin n → ℝ)) (nhds 0) := by
    have h := hu₁_decay.sub hu₂_decay
    simp only [sub_zero] at h
    exact h
  have hw_cont : Continuous w := (hu₁_smooth.sub hu₂_smooth).continuous
  have hw_bdd : ∃ M : ℝ, ∀ y, w y ≤ M := by
    have hcpt : IsCompact (insert (0 : ℝ) (Set.range w)) :=
      hw_decay.isCompact_insert_range_of_cocompact hw_cont
    have hbdd : Bornology.IsBounded (Set.range w) :=
      (hcpt.isBounded.subset (Set.subset_insert _ _))
    rw [Metric.isBounded_iff_subset_ball 0] at hbdd
    obtain ⟨r, hr⟩ := hbdd
    exact ⟨r, fun y => by
      have hwy : w y ∈ Set.range w := Set.mem_range_self y
      have := hr hwy
      rw [Metric.mem_ball, Real.dist_eq] at this
      linarith [abs_lt.mp this |>.2]⟩
  obtain ⟨M, hM⟩ := hw_bdd
  obtain ⟨c, hc⟩ := PoissonHarnack.liouville_theorem w hw_harmonic hw_smooth2 M (Or.inr hM)
  have hc_zero : c = 0 := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin n → ℝ) := Function.nontrivial
    haveI : NoncompactSpace (Fin n → ℝ) := inferInstance
    have hw_eq_c : w = Function.const _ c := funext hc
    have htends_c : Filter.Tendsto w (Filter.cocompact (Fin n → ℝ)) (nhds c) := by
      rw [hw_eq_c]; exact tendsto_const_nhds
    exact (tendsto_nhds_unique hw_decay htends_c).symm
  have := hc x
  linarith [hc_zero]

end LaplacePoisson

namespace LaplacePoisson

/--
[dirichlet_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma dirichlet_uniqueness
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {u₁ u₂ : (Fin n → ℝ) → ℝ}
  {f g : (Fin n → ℝ) → ℝ}
-- given
  (hn : 0 < n)
  (hΩ : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω)
  (hu₁_reg : ContDiffOn ℝ 2 u₁ Ω)
  (hu₁_cont : ContinuousOn u₁ (closure Ω))
  (hu₂_reg : ContDiffOn ℝ 2 u₂ Ω)
  (hu₂_cont : ContinuousOn u₂ (closure Ω))
  (hu₁_pde : ∀ x ∈ Ω, laplacianLP u₁ x = f x)
  (hu₂_pde : ∀ x ∈ Ω, laplacianLP u₂ x = f x)
  (hu₁_bdy : ∀ σ ∈ frontier Ω, u₁ σ = g σ)
  (hu₂_bdy : ∀ σ ∈ frontier Ω, u₂ σ = g σ) :
-- imply
  ∀ x ∈ closure Ω, u₁ x = u₂ x := by
-- proof
  have hw_harm : CM7.IsHarmonic (fun x => u₁ x - u₂ x) Ω := by
    constructor
    · exact hu₁_reg.sub hu₂_reg
    · intro x hx
      have hsub := CM7.laplacian_sub hΩ hu₁_reg hu₂_reg hx
      change CM7.Laplacian n (fun x => u₁ x - u₂ x) x = 0
      rw [hsub]
      have h1 : CM7.Laplacian n u₁ x = f x := hu₁_pde x hx
      have h2 : CM7.Laplacian n u₂ x = f x := hu₂_pde x hx
      linarith
  have hbdy : ∀ x ∈ frontier Ω, u₁ x = u₂ x := by
    intro x hx
    rw [hu₁_bdy x hx, hu₂_bdy x hx]
  have h_on_Ω : ∀ x ∈ Ω, u₁ x = u₂ x := by
    have h := @CM7.dirichlet_uniqueness n hn Ω hΩ hΩc hΩb
      (fun x => u₁ x - u₂ x) (fun _ => (0 : ℝ))
      hw_harm
      ⟨contDiffOn_const, fun x _ => by simp [CM7.Laplacian]⟩
      (fun x hx => by simp [hbdy x hx])
      (hu₁_cont.sub hu₂_cont)
      continuousOn_const
    intro x hx
    have := h x hx
    linarith
  intro x hx
  have h_cases : x ∈ Ω ∨ x ∈ frontier Ω := by
    rw [closure_eq_interior_union_frontier] at hx
    rwa [hΩ.interior_eq] at hx
  obtain hxΩ | hxF := h_cases
  · exact h_on_Ω x hxΩ
  · exact hbdy x hxF

end LaplacePoisson

namespace LaplacePoisson

/--
[sphereIntegralLP_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma sphereIntegralLP_const_mul
  {n : ℕ}
  {x : Fin n → ℝ}
  {ε : ℝ}
  {c : ℝ}
  {f : (Fin n → ℝ) → ℝ} :
-- imply
  sphereIntegralLP x ε (fun σ => c * f σ) = c * sphereIntegralLP x ε f := by
-- proof
  simp only [sphereIntegralLP]
  rw [show (fun σ : Fin n → ℝ => c * f σ) = (fun σ => c • f σ) from by ext σ; rfl]
  rw [MeasureTheory.integral_smul]
  rfl

end LaplacePoisson

namespace LaplacePoisson

/--
[sphereIntegralLP_congr_on_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma sphereIntegralLP_congr_on_sphere
  {n : ℕ}
  {x : Fin n → ℝ}
  {ε : ℝ}
  {f g : (Fin n → ℝ) → ℝ}
-- given
  (h : ∀ σ, σ ∈ Metric.sphere x ε → f σ = g σ) :
-- imply
  sphereIntegralLP x ε f = sphereIntegralLP x ε g := by
-- proof
  simp only [sphereIntegralLP]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_frontier
    (fun σ hσ => h σ (Metric.frontier_ball_subset_sphere hσ))

end LaplacePoisson

namespace LaplacePoisson

/--
[oscillation_sphere_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma oscillation_sphere_tendsto_zero
  {n : ℕ}
  {u : (Fin n → ℝ) → ℝ}
  {Ω : Set (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (hu : ContDiffOn ℝ 2 u (closure Ω))
  (hΩ : IsOpen Ω)
  (hx : x ∈ Ω) :
-- imply
  Filter.Tendsto (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
-- proof
  have hcont : ContinuousOn u (closure Ω) := hu.continuousOn
  have hx_nhds : closure Ω ∈ nhds x :=
    _root_.mem_nhds_iff.mpr ⟨Ω, subset_closure, hΩ, hx⟩
  have hca : ContinuousAt u x := hcont.continuousAt hx_nhds
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨η, hη, hηu⟩ := hca (δ / 2) (by linarith)
  refine ⟨η, hη, fun ε hε_mem hε_dist => ?_⟩
  rw [mem_Ioi] at hε_mem
  simp [abs_of_pos hε_mem] at hε_dist
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg (fun σ => Real.iSup_nonneg (fun _ => abs_nonneg _))
  rw [abs_of_nonneg hnn]
  have hbnd : ∀ σ : Fin n → ℝ, ⨆ (_ : σ ∈ Metric.sphere x ε), |u σ - u x| ≤ δ / 2 := by
    intro σ
    by_cases hσ : σ ∈ Metric.sphere x ε
    ·
      haveI : Unique (σ ∈ Metric.sphere x ε) := ⟨⟨hσ⟩, fun _ => Subsingleton.elim _ _⟩
      rw [ciSup_unique]
      rw [Metric.mem_sphere] at hσ
      have hdist : dist σ x < η := by rw [hσ]; exact hε_dist
      have := hηu hdist
      rw [Real.dist_eq] at this
      linarith
    ·
      haveI : IsEmpty (σ ∈ Metric.sphere x ε) := isEmpty_iff.mpr hσ
      rw [Real.iSup_of_isEmpty]
      linarith
  calc ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|
    ≤ δ / 2 := ciSup_le hbnd
    _ < δ := by linarith

end LaplacePoisson

namespace LaplacePoisson

/--
[volume_integral_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma volume_integral_combination
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {gf : GreenFunctionLP n Ω}
  {f : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hΦf : IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω)
  (hGf : IntegrableOn (fun y => gf.G x y * f y) Ω) :
-- imply
  let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y) let φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y (-(∫ y in Ω, Φ y * f y) + (∫ y in Ω, φ y * f y) = -(∫ y in Ω, f y * gf.G x y)) := by
-- proof
  intro Φ φ
  have integrand_eq : (∫ y in Ω, φ y * f y) = ∫ y in Ω, (Φ y * f y - gf.G x y * f y) := by
    congr 1; ext y; show (Φ y - gf.G x y) * f y = Φ y * f y - gf.G x y * f y; ring
  rw [integrand_eq]
  rw [MeasureTheory.integral_sub hΦf hGf]
  have h_comm : (∫ y in Ω, gf.G x y * f y) = ∫ y in Ω, f y * gf.G x y := by
    congr 1; ext y; ring
  linarith [h_comm]

end LaplacePoisson

namespace LaplacePoisson

/--
[surface_integral_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma surface_integral_combination
  {n : ℕ}
  {Ω : Set (Fin n → ℝ)}
  {gf : GreenFunctionLP n Ω}
  {g : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hΦ_diff : ∀ σ, DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ)
  (hG_diff : ∀ σ, DifferentiableAt ℝ (fun z => gf.G x z) σ)
  (h1_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ) (frontier Ω) (surfaceMeasure Ω))
  (h2_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) (frontier Ω) (surfaceMeasure Ω)) :
-- imply
  let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y) let φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y (-(surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ)) + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) = -(surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ))) := by
-- proof
  intro Φ φ
  have normalDeriv_split : ∀ σ, normalDerivLP Ω φ σ =
    normalDerivLP Ω Φ σ - normalDerivLP Ω (fun z => gf.G x z) σ := by
    intro σ
    unfold normalDerivLP
    change (∑ i : Fin n, (fderiv ℝ (fun y => fundamentalSolution n (x - y) - gf.G x y) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i) =
      (∑ i : Fin n, (fderiv ℝ (fun y => fundamentalSolution n (x - y)) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i) -
      (∑ i : Fin n, (fderiv ℝ (fun z => gf.G x z) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i)
    have heq : (fun y => fundamentalSolution n (x - y) - gf.G x y) = (fun y => fundamentalSolution n (x - y)) - (fun z => gf.G x z) := by
      ext; simp [Pi.sub_apply]
    rw [heq, fderiv_sub (hΦ_diff σ) (hG_diff σ)]
    simp only [ContinuousLinearMap.sub_apply]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i; ring
  have integrand_eq : surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) =
    surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ - g σ * normalDerivLP Ω (fun z => gf.G x z) σ) := by
    unfold surfaceIntegralLP
    apply setIntegral_congr_fun measurableSet_frontier
    intro σ _; simp only []; rw [normalDeriv_split σ]; ring
  rw [integrand_eq]
  unfold surfaceIntegralLP
  rw [MeasureTheory.integral_sub h1_int h2_int]
  ring

end LaplacePoisson

namespace LaplacePoisson

/--
[euclideanSpace_norm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma euclideanSpace_norm_sq
  {v : EuclideanSpace ℝ (Fin 3)} :
-- imply
  ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
-- proof
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  congr 1; ext i; simp [Real.norm_eq_abs, sq_abs]

end LaplacePoisson

namespace LaplacePoisson

/--
[dirichlet_uniquenessE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma dirichlet_uniquenessE
  {n : ℕ}
  {Ω : Set (EuclideanSpace ℝ (Fin n))}
  {u₁ u₂ : EuclideanSpace ℝ (Fin n) → ℝ}
  {f g : EuclideanSpace ℝ (Fin n) → ℝ}
-- given
  (hn : 0 < n)
  (hΩ : IsOpen Ω)
  (hΩc : IsConnected Ω)
  (hΩb : Bornology.IsBounded Ω)
  (hu₁_reg : ContDiffOn ℝ 2 u₁ Ω)
  (hu₁_cont : ContinuousOn u₁ (closure Ω))
  (hu₂_reg : ContDiffOn ℝ 2 u₂ Ω)
  (hu₂_cont : ContinuousOn u₂ (closure Ω))
  (hu₁_pde : ∀ x ∈ Ω, laplacianE u₁ x = f x)
  (hu₂_pde : ∀ x ∈ Ω, laplacianE u₂ x = f x)
  (hu₁_bdy : ∀ σ ∈ frontier Ω, u₁ σ = g σ)
  (hu₂_bdy : ∀ σ ∈ frontier Ω, u₂ σ = g σ) :
-- imply
  ∀ x ∈ closure Ω, u₁ x = u₂ x := by
-- proof
  set e := EuclideanSpace.equiv (Fin n) ℝ with he_def
  have h_lap : ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)),
    laplacianLP (u ∘ ⇑e.symm) (e x) = laplacianE u x := by
    intro u x
    simp only [laplacianLP, laplacianE]
    congr 1; ext i
    have h_single : e.symm (Pi.single i (1 : ℝ)) = EuclideanSpace.single i (1 : ℝ) := by
      apply e.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      rfl
    have h_inner : (fun z => fderiv ℝ (u ∘ ⇑e.symm) z (Pi.single i 1)) =
      (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) ∘ ⇑e.symm := by
      ext z
      rw [Function.comp_apply, e.symm.comp_right_fderiv (f := u)]
      simp [ContinuousLinearMap.comp_apply, h_single]
    rw [h_inner, e.symm.comp_right_fderiv]
    simp [ContinuousLinearMap.comp_apply, h_single, ContinuousLinearEquiv.symm_apply_apply]
  have h_uniq := dirichlet_uniqueness hn
    (e '' Ω)
    (e.toHomeomorph.isOpenMap _ hΩ)
    (hΩc.image _ e.continuous.continuousOn)
    (e.lipschitz.isBounded_image hΩb)
    (u₁ ∘ ⇑e.symm) (u₂ ∘ ⇑e.symm) (f ∘ ⇑e.symm) (g ∘ ⇑e.symm)
    (hu₁_reg.comp e.symm.contDiff.contDiffOn (by
      intro z hz; simp [Set.mem_image] at hz; obtain ⟨w, hw, rfl⟩ := hz; simpa))
    (hu₁_cont.comp e.symm.continuousOn (by
      intro z hz
      have : e.symm z ∈ closure Ω := by
        rw [show closure (e '' Ω) = e '' closure Ω from (e.toHomeomorph.image_closure Ω).symm] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        rwa [← hwz]; simp
      exact this))
    (hu₂_reg.comp e.symm.contDiff.contDiffOn (by
      intro z hz; simp [Set.mem_image] at hz; obtain ⟨w, hw, rfl⟩ := hz; simpa))
    (hu₂_cont.comp e.symm.continuousOn (by
      intro z hz
      have : e.symm z ∈ closure Ω := by
        rw [show closure (e '' Ω) = e '' closure Ω from (e.toHomeomorph.image_closure Ω).symm] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        rwa [← hwz]; simp
      exact this))
    (fun z hz => by
      simp [Set.mem_image] at hz; obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      rw [h_lap u₁ y]; exact hu₁_pde y hy)
    (fun z hz => by
      simp [Set.mem_image] at hz; obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      rw [h_lap u₂ y]; exact hu₂_pde y hy)
    (fun σ hσ => by
      have hfr : frontier (⇑e '' Ω) = ⇑e '' frontier Ω :=
        (e.toHomeomorph.image_frontier Ω).symm
      rw [hfr] at hσ
      simp [Set.mem_image] at hσ; obtain ⟨y, hy, rfl⟩ := hσ
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      exact hu₁_bdy y hy)
    (fun σ hσ => by
      have hfr : frontier (⇑e '' Ω) = ⇑e '' frontier Ω :=
        (e.toHomeomorph.image_frontier Ω).symm
      rw [hfr] at hσ
      simp [Set.mem_image] at hσ; obtain ⟨y, hy, rfl⟩ := hσ
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      exact hu₂_bdy y hy)
  intro x hx
  have hx' : e x ∈ closure (⇑e '' Ω) := by
    have hcl : closure (⇑e '' Ω) = ⇑e '' closure Ω :=
      (e.toHomeomorph.image_closure Ω).symm
    rw [hcl]; exact Set.mem_image_of_mem e hx
  have h := h_uniq (e x) hx'
  simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

end LaplacePoisson

namespace LaplacePoisson

/--
[kelvinImageE_not_in_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM7/LaplacePoisson.lean)
-/
@[path]
lemma kelvinImageE_not_in_ball
  {p : EuclideanSpace ℝ (Fin 3)}
  {R : ℝ}
  {x : EuclideanSpace ℝ (Fin 3)}
-- given
  (hR : 0 < R)
  (hx : x ∈ Metric.ball p R)
  (hxp : x ≠ p) :
-- imply
  kelvinImageE p R x ∉ Metric.ball p R := by
-- proof
  have hxp_pos : (0 : ℝ) < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
  have hxp_lt_R : ‖x - p‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, not_lt, dist_eq_norm]
  have h1 : kelvinImageE p R x - p = (R / ‖x - p‖) ^ 2 • (x - p) := by
    simp only [kelvinImageE, add_sub_cancel_left]
  rw [h1, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  have hxp_ne : ‖x - p‖ ≠ 0 := ne_of_gt hxp_pos
  have h2 : (R / ‖x - p‖) ^ 2 * ‖x - p‖ = R ^ 2 / ‖x - p‖ := by field_simp
  rw [h2]
  rw [le_div_iff₀ hxp_pos]
  nlinarith [sq_nonneg (R - ‖x - p‖)]

end LaplacePoisson


-- created on 2026-10-23
