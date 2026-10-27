import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
open StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[complex_wedgeIntegral_tendsto_of_locallyUniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma complex_wedgeIntegral_tendsto_of_locallyUniform_eq
  {F : Nat -> Complex -> Complex}
  {f : Complex -> Complex}
  {z w : Complex}
-- given
  (hF : forall n, Continuous (F n))
  (hlimit : TendstoLocallyUniformlyOn F f atTop Set.univ) :
-- imply
  Tendsto (fun n => Complex.wedgeIntegral z w (F n)) atTop (nhds (Complex.wedgeIntegral z w f)) := by
-- proof
  apply StatMech.Universality.complex_wedgeIntegral_tendsto_of_locallyUniform hF hlimit z w

/--
[continuous_wedgeContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma continuous_wedgeContour_eq
-- given
  (f : Complex -> Complex)
  (hf : Continuous f) :
-- imply
  Continuous (fun p : Complex × Complex => Complex.wedgeIntegral p.1 p.2 f + Complex.wedgeIntegral p.2 p.1 f) := by
-- proof
  apply StatMech.Universality.continuous_wedgeContour f hf

/--
[VanishingRectangleContourError.contour_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma contour_tendsto_zero_eq
  {F : Nat -> Complex -> Complex}
  {H : VanishingRectangleContourError F}
  {z w : Complex} :
-- imply
  Tendsto (fun n => Complex.wedgeIntegral z w (F n) + Complex.wedgeIntegral w z (F n)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.VanishingRectangleContourError.contour_tendsto_zero H z w

/--
[VanishingRectangleContourError.contour_tendsto_zero_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma contour_tendsto_zero_comp_eq
  {F : Nat -> Complex -> Complex}
  {H : VanishingRectangleContourError F}
  {sigma : Nat -> Nat}
  {z w : Complex}
-- given
  (hsigma : Tendsto sigma atTop atTop) :
-- imply
  Tendsto (fun n => Complex.wedgeIntegral z w (F (sigma n)) + Complex.wedgeIntegral w z (F (sigma n))) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.VanishingRectangleContourError.contour_tendsto_zero_comp H hsigma z w

/--
[norm_wedgeContour_le_of_uniformNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_wedgeContour_le_of_uniformNorm_eq
  {epsilon : Real}
  {z w : Complex}
-- given
  (F : Complex -> Complex)
  (hF : forall z, norm (F z) <= epsilon) :
-- imply
  norm (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) <= 2 * epsilon * (|w.re - z.re| + |w.im - z.im|) := by
-- proof
  apply StatMech.Universality.norm_wedgeContour_le_of_uniformNorm F epsilon hF z w

/--
[complexDisplacementIntegral_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma complexDisplacementIntegral_reverse_eq
  {a v : Complex}
-- given
  (f : Complex -> Complex) :
-- imply
  complexDisplacementIntegral f (a + v) (-v) = -complexDisplacementIntegral f a v := by
-- proof
  apply StatMech.Universality.complexDisplacementIntegral_reverse f a v

/--
[complexDisplacementIntegral_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma complexDisplacementIntegral_ofReal_eq
  {x y d : Real}
-- given
  (f : Complex -> Complex) :
-- imply
  complexDisplacementIntegral f (x + y * Complex.I) d = ∫ s : Real in x..x + d, f (s + y * Complex.I) := by
-- proof
  apply StatMech.Universality.complexDisplacementIntegral_ofReal f x y d

/--
[complexDisplacementIntegral_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma complexDisplacementIntegral_mul_I_eq
  {x y d : Real}
-- given
  (f : Complex -> Complex) :
-- imply
  complexDisplacementIntegral f (x + y * Complex.I) ((d : Complex) * Complex.I) = Complex.I * ∫ s : Real in y..y + d, f (x + s * Complex.I) := by
-- proof
  apply StatMech.Universality.complexDisplacementIntegral_mul_I f x y d

/--
[axisRectangleDisplacementContour_eq_wedgeContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma axisRectangleDisplacementContour_eq_wedgeContour_eq
-- given
  (f : Complex -> Complex)
  (x y width height : Real) :
-- imply
  complexDisplacementIntegral f (x + y * Complex.I) width + complexDisplacementIntegral f ((x + width : Real) + y * Complex.I) ((height : Complex) * Complex.I) + complexDisplacementIntegral f ((x + width : Real) + (y + height : Real) * Complex.I) ((-width : Real) : Complex) + complexDisplacementIntegral f (x + (y + height : Real) * Complex.I) ((-height : Real) * Complex.I) = Complex.wedgeIntegral (x + y * Complex.I) ((x + width : Real) + (y + height : Real) * Complex.I) f + Complex.wedgeIntegral ((x + width : Real) + (y + height : Real) * Complex.I) (x + y * Complex.I) f := by
-- proof
  apply StatMech.Universality.axisRectangleDisplacementContour_eq_wedgeContour f x y width height

/--
[sum_horizontalComplexDisplacementIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma sum_horizontalComplexDisplacementIntegral_eq
  {x y mesh : Real}
  {N : Nat}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f) :
-- imply
  (∑ k ∈ Finset.range N, complexDisplacementIntegral f ((x + (k : Real) * mesh : Real) + y * Complex.I) mesh) = complexDisplacementIntegral f (x + y * Complex.I) ((((N : Real) * mesh) : Real) : Complex) := by
-- proof
  apply StatMech.Universality.sum_horizontalComplexDisplacementIntegral f hf x y mesh N

/--
[sum_verticalComplexDisplacementIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma sum_verticalComplexDisplacementIntegral_eq
  {x y mesh : Real}
  {N : Nat}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f) :
-- imply
  (∑ k ∈ Finset.range N, complexDisplacementIntegral f (x + (y + (k : Real) * mesh : Real) * Complex.I) ((mesh : Complex) * Complex.I)) = complexDisplacementIntegral f (x + y * Complex.I) (((N : Real) * mesh : Real) * Complex.I) := by
-- proof
  apply StatMech.Universality.sum_verticalComplexDisplacementIntegral f hf x y mesh N

/--
[axisTwoEdgeStaircase_base_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma axisTwoEdgeStaircase_base_norm_le_eq
  {x y mesh : Real}
-- given
  (width height : Nat)
  (hmesh : 0 ≤ mesh) :
-- imply
  let p : Complex := x + y * Complex.I (∀ k < width, norm (((x + (k : Real) * mesh : Real) + y * Complex.I) - p) ≤ (width : Real) * mesh + (height : Real) * mesh) ∧ (∀ k < height, norm (((x + (width : Real) * mesh : Real) + (y + (k : Real) * mesh : Real) * Complex.I) - p) ≤ (width : Real) * mesh + (height : Real) * mesh) ∧ (∀ k < width, norm (((x + (width : Real) * mesh - (k : Real) * mesh : Real) + (y + (height : Real) * mesh : Real) * Complex.I) - p) ≤ (width : Real) * mesh + (height : Real) * mesh) ∧ (∀ k < height, norm ((x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) * Complex.I) - p) ≤ (width : Real) * mesh + (height : Real) * mesh) := by
-- proof
  apply StatMech.Universality.axisTwoEdgeStaircase_base_norm_le x y mesh width height hmesh

/--
[axisMacroDirectContour_eq_wedgeContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma axisMacroDirectContour_eq_wedgeContour_eq
  {x y mesh : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (width height : Nat) :
-- imply
  axisMacroDirectContour f x y mesh width height = Complex.wedgeIntegral (x + y * Complex.I) ((x + (width : Real) * mesh : Real) + (y + (height : Real) * mesh : Real) * Complex.I) f + Complex.wedgeIntegral ((x + (width : Real) * mesh : Real) + (y + (height : Real) * mesh : Real) * Complex.I) (x + y * Complex.I) f := by
-- proof
  apply StatMech.Universality.axisMacroDirectContour_eq_wedgeContour f hf x y mesh width height

/--
[norm_complexDisplacementIntegral_sub_const_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sub_const_mul_le_eq
  {a v c : Complex}
  {epsilon : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hosc : ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a + (t : Complex) * v) - c) <= epsilon) :
-- imply
  norm (complexDisplacementIntegral f a v - c * v) <= epsilon * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sub_const_mul_le f hf a v c epsilon hosc

/--
[norm_complexDisplacementIntegral_sub_le_of_uniformNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_complexDisplacementIntegral_sub_le_of_uniformNorm_eq
  {a v : Complex}
  {epsilon : Real}
-- given
  (F G : Complex -> Complex)
  (hF : Continuous F)
  (hG : Continuous G)
  (herror : ∀ t ∈ Set.Icc (0 : Real) 1, norm (F (a + (t : Complex) * v) - G (a + (t : Complex) * v)) ≤ epsilon) :
-- imply
  norm (complexDisplacementIntegral F a v - complexDisplacementIntegral G a v) ≤ epsilon * norm v := by
-- proof
  apply StatMech.Universality.norm_complexDisplacementIntegral_sub_le_of_uniformNorm F G hF hG a v epsilon herror

/--
[norm_twoStepDisplacementIntegral_sub_direct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_twoStepDisplacementIntegral_sub_direct_le_eq
  {a u v c : Complex}
  {epsilon : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (hu : ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a + (t : Complex) * u) - c) <= epsilon)
  (hv : ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a + u + (t : Complex) * v) - c) <= epsilon)
  (hdirect : ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a + (t : Complex) * (u + v)) - c) <= epsilon) :
-- imply
  norm (complexDisplacementIntegral f a u + complexDisplacementIntegral f (a + u) v - complexDisplacementIntegral f a (u + v)) <= epsilon * (norm u + norm v + norm (u + v)) := by
-- proof
  apply StatMech.Universality.norm_twoStepDisplacementIntegral_sub_direct_le f hf a u v c epsilon hu hv hdirect

/--
[norm_twoStepDisplacementIntegral_sub_direct_le_of_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_twoStepDisplacementIntegral_sub_direct_le_of_ball_eq
  {a u v : Complex}
  {epsilon radius : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (huNorm : norm u ≤ radius)
  (hvNorm : norm v ≤ radius)
  (hosc : ∀ q, norm (q - a) ≤ 2 * radius -> norm (f q - f a) ≤ epsilon) :
-- imply
  norm (complexDisplacementIntegral f a u + complexDisplacementIntegral f (a + u) v - complexDisplacementIntegral f a (u + v)) ≤ epsilon * (norm u + norm v + norm (u + v)) := by
-- proof
  apply StatMech.Universality.norm_twoStepDisplacementIntegral_sub_direct_le_of_ball f hf a u v epsilon radius huNorm hvNorm hosc

/--
[norm_sum_twoStepDisplacementIntegral_sub_direct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_sum_twoStepDisplacementIntegral_sub_direct_le_eq
  {N : Nat}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (a u v c : Nat -> Complex)
  (epsilon : Nat -> Real)
  (hu : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a k + (t : Complex) * u k) - c k) <= epsilon k)
  (hv : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a k + u k + (t : Complex) * v k) - c k) <= epsilon k)
  (hdirect : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1, norm (f (a k + (t : Complex) * (u k + v k)) - c k) <= epsilon k) :
-- imply
  norm (∑ k ∈ Finset.range N, (complexDisplacementIntegral f (a k) (u k) + complexDisplacementIntegral f (a k + u k) (v k) - complexDisplacementIntegral f (a k) (u k + v k))) <= ∑ k ∈ Finset.range N, epsilon k * (norm (u k) + norm (v k) + norm (u k + v k)) := by
-- proof
  apply StatMech.Universality.norm_sum_twoStepDisplacementIntegral_sub_direct_le f hf N a u v c epsilon hu hv hdirect

/--
[norm_sum_twoEdgePath_sub_direct_le_of_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_sum_twoEdgePath_sub_direct_le_of_ball_eq
  {N : Nat}
  {u v : Complex}
  {epsilon radius : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (a : Nat -> Complex)
  (huNorm : norm u ≤ radius)
  (hvNorm : norm v ≤ radius)
  (hosc : ∀ k < N, ∀ q, norm (q - a k) ≤ 2 * radius -> norm (f q - f (a k)) ≤ epsilon) :
-- imply
  norm ((∑ k ∈ Finset.range N, (complexDisplacementIntegral f (a k) u + complexDisplacementIntegral f (a k + u) v)) - ∑ k ∈ Finset.range N, complexDisplacementIntegral f (a k) (u + v)) ≤ ∑ k ∈ Finset.range N, epsilon * (norm u + norm v + norm (u + v)) := by
-- proof
  apply StatMech.Universality.norm_sum_twoEdgePath_sub_direct_le_of_ball f hf N a u v epsilon radius huNorm hvNorm hosc

/--
[norm_sum_twoEdgePath_sub_le_of_uniformNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_sum_twoEdgePath_sub_le_of_uniformNorm_eq
  {N : Nat}
  {u v : Complex}
  {epsilon : Real}
-- given
  (F G : Complex -> Complex)
  (hF : Continuous F)
  (hG : Continuous G)
  (a : Nat -> Complex)
  (herror : ∀ k < N, ∀ q, (∃ t ∈ Set.Icc (0 : Real) 1, q = a k + (t : Complex) * u) ∨ (∃ t ∈ Set.Icc (0 : Real) 1, q = a k + u + (t : Complex) * v) -> norm (F q - G q) ≤ epsilon) :
-- imply
  norm ((∑ k ∈ Finset.range N, (complexDisplacementIntegral F (a k) u + complexDisplacementIntegral F (a k + u) v)) - ∑ k ∈ Finset.range N, (complexDisplacementIntegral G (a k) u + complexDisplacementIntegral G (a k + u) v)) ≤ ∑ k ∈ Finset.range N, epsilon * (norm u + norm v) := by
-- proof
  apply StatMech.Universality.norm_sum_twoEdgePath_sub_le_of_uniformNorm F G hF hG N a u v epsilon herror

/--
[norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_uniformNorm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_uniformNorm_eq
  {x y mesh : Real}
  {epsilon : Real}
-- given
  (F G : Complex -> Complex)
  (hF : Continuous F)
  (hG : Continuous G)
  (width height : Nat)
  (hmesh : 0 < mesh)
  (herror : ∀ q, norm (F q - G q) ≤ epsilon) :
-- imply
  norm (axisTwoEdgeStaircasePathIntegral F x y mesh width height - axisTwoEdgeStaircasePathIntegral G x y mesh width height) ≤ 4 * epsilon * mesh * (width + height) := by
-- proof
  apply StatMech.Universality.norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_uniformNorm F G hF hG x y mesh width height epsilon hmesh herror

/--
[VanishingRectangleContourError.isConservativeOn_subsequentialLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma isConservativeOn_subsequentialLimit_eq
  {F : Nat -> Complex -> Complex}
  {H : VanishingRectangleContourError F}
  {sigma : Nat -> Nat}
  {f : Complex -> Complex}
-- given
  (hF : forall n, Continuous (F n))
  (hsigma : Tendsto sigma atTop atTop)
  (hlimit : TendstoLocallyUniformlyOn (fun n => F (sigma n)) f atTop Set.univ) :
-- imply
  Complex.IsConservativeOn f Set.univ := by
-- proof
  apply StatMech.Universality.VanishingRectangleContourError.isConservativeOn_subsequentialLimit H hF hsigma hlimit

/--
[isingCellCRAt_conj_radialGridPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma isingCellCRAt_conj_radialGridPosition_eq
  {mesh : Real}
  {i j : Nat} :
-- imply
  IsingCellCRAt (fun a b => (starRingEnd Complex) (isingRadialGridPosition mesh a b)) i j := by
-- proof
  apply StatMech.Universality.isingCellCRAt_conj_radialGridPosition mesh i j

/--
[isingCellCRAt_radialGridPosition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma isingCellCRAt_radialGridPosition_iff_eq
  {mesh : Real}
  {i j : Nat} :
-- imply
  IsingCellCRAt (fun a b => isingRadialGridPosition mesh a b) i j <-> mesh = 0 := by
-- proof
  apply StatMech.Universality.isingCellCRAt_radialGridPosition_iff mesh i j

/--
[reflectedRadialBilinearCellContour_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellContour_eq_eq
  {mesh : Real}
  {a00 a10 a01 a11 : Complex} :
-- imply
  reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 = (mesh : Complex) / 2 * ((a10 - a01) + Complex.I * (a11 - a00)) := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellContour_eq mesh a00 a10 a01 a11

/--
[intervalIntegral_complexAffine_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma intervalIntegral_complexAffine_unit_eq
  {a b : Complex} :
-- imply
  (∫ x : Real in 0..1, ((1 - x : Real) : Complex) * a + (x : Complex) * b) = (a + b) / 2 := by
-- proof
  apply StatMech.Universality.intervalIntegral_complexAffine_unit a b

/--
[complexDisplacementIntegral_eq_average_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma complexDisplacementIntegral_eq_average_mul_eq
  {a v A B : Complex}
-- given
  (f : Complex -> Complex)
  (haffine : ∀ t ∈ Set.Icc (0 : Real) 1, f (a + (t : Complex) * v) = ((1 - t : Real) : Complex) * A + (t : Complex) * B) :
-- imply
  complexDisplacementIntegral f a v = (A + B) / 2 * v := by
-- proof
  apply StatMech.Universality.complexDisplacementIntegral_eq_average_mul f a v A B haffine

/--
[reflectedRadialBilinearCellPathIntegral_eq_contour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellPathIntegral_eq_contour_eq
  {mesh : Real}
  {a00 a10 a01 a11 : Complex} :
-- imply
  reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 = reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellPathIntegral_eq_contour mesh a00 a10 a01 a11

/--
[reflectedRadialBilinearCellContour_eq_zero_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellContour_eq_zero_of_cellCR_eq
  {mesh : Real}
  {a00 a10 a01 a11 : Complex}
-- given
  (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
-- imply
  reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh a00 a10 a01 a11 hCR

/--
[reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR_eq
  {mesh : Real}
  {a00 a10 a01 a11 : Complex}
-- given
  (hCR : a01 - a10 = Complex.I * (a11 - a00)) :
-- imply
  reflectedRadialBilinearCellPathIntegral mesh a00 a10 a01 a11 = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellPathIntegral_eq_zero_of_cellCR mesh a00 a10 a01 a11 hCR

/--
[IsingCellCRAt.div_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma div_const_eq
  {F : Nat -> Nat -> Complex}
  {i j : Nat}
  {c : Complex}
-- given
  (hCR : IsingCellCRAt F i j) :
-- imply
  IsingCellCRAt (fun a b => F a b / c) i j := by
-- proof
  apply StatMech.Universality.IsingCellCRAt.div_const hCR c

/--
[reflectedRadialBilinearCellContour_eq_edgeCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellContour_eq_edgeCoboundary_eq
  {mesh : Real}
  {i j : Nat}
-- given
  (F : Nat -> Nat -> Complex) :
-- imply
  reflectedRadialBilinearCellContour mesh (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) = reflectedRadialHorizontalEdgeIntegral mesh F i j + reflectedRadialVerticalEdgeIntegral mesh F (i + 1) j - reflectedRadialHorizontalEdgeIntegral mesh F i (j + 1) - reflectedRadialVerticalEdgeIntegral mesh F i j := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellContour_eq_edgeCoboundary mesh F i j

/--
[sum_range_add_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma sum_range_add_one_sub_eq
  {base n : Nat}
-- given
  (f : Nat -> Complex) :
-- imply
  (∑ k ∈ Finset.range n, (f (base + k + 1) - f (base + k))) = f (base + n) - f base := by
-- proof
  apply StatMech.Universality.sum_range_add_one_sub f base n

/--
[sum_range_sub_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma sum_range_sub_add_one_eq
  {base n : Nat}
-- given
  (f : Nat -> Complex) :
-- imply
  (∑ k ∈ Finset.range n, (f (base + k) - f (base + k + 1))) = f base - f (base + n) := by
-- proof
  apply StatMech.Universality.sum_range_sub_add_one f base n

/--
[reflectedRadialDiscretePrimitive_succ_j](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialDiscretePrimitive_succ_j_eq
  {i0 j0 a b : Nat}
-- given
  (H V : Nat -> Nat -> Complex) :
-- imply
  reflectedRadialDiscretePrimitive H V i0 j0 a (b + 1) - reflectedRadialDiscretePrimitive H V i0 j0 a b = V (i0 + a) (j0 + b) := by
-- proof
  apply StatMech.Universality.reflectedRadialDiscretePrimitive_succ_j H V i0 j0 a b

/--
[reflectedRadialDiscretePrimitive_succ_i](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialDiscretePrimitive_succ_i_eq
  {i0 j0 a b : Nat}
-- given
  (H V : Nat -> Nat -> Complex)
  (hcurl : ∀ y < b, H (i0 + a) (j0 + y) + V (i0 + a + 1) (j0 + y) - H (i0 + a) (j0 + y + 1) - V (i0 + a) (j0 + y) = 0) :
-- imply
  reflectedRadialDiscretePrimitive H V i0 j0 (a + 1) b - reflectedRadialDiscretePrimitive H V i0 j0 a b = H (i0 + a) (j0 + b) := by
-- proof
  apply StatMech.Universality.reflectedRadialDiscretePrimitive_succ_i H V i0 j0 a b hcurl

/--
[reflectedRadialDiscretePrimitive_succ_i_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialDiscretePrimitive_succ_i_of_cellCR_eq
  {mesh : Real}
  {i0 j0 a b : Nat}
-- given
  (F : Nat -> Nat -> Complex)
  (hCR : ∀ y < b, IsingCellCRAt F (i0 + a) (j0 + y)) :
-- imply
  reflectedRadialDiscretePrimitive (reflectedRadialHorizontalEdgeIntegral mesh F) (reflectedRadialVerticalEdgeIntegral mesh F) i0 j0 (a + 1) b - reflectedRadialDiscretePrimitive (reflectedRadialHorizontalEdgeIntegral mesh F) (reflectedRadialVerticalEdgeIntegral mesh F) i0 j0 a b = reflectedRadialHorizontalEdgeIntegral mesh F (i0 + a) (j0 + b) := by
-- proof
  apply StatMech.Universality.reflectedRadialDiscretePrimitive_succ_i_of_cellCR mesh F i0 j0 a b hCR

/--
[reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge_eq
  {mesh : Real}
-- given
  (f : Complex -> Complex)
  (n i0 j0 width height : Nat) :
-- imply
  let p := isingReflectedCenteredRadialGridPosition mesh n (i0 + height) j0 reflectedRadialAxisStaircasePathIntegral f mesh n i0 j0 width height = axisTwoEdgeStaircasePathIntegral f p.re p.im mesh width height := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisStaircasePathIntegral_eq_axisTwoEdge f mesh n i0 j0 width height

/--
[reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR_eq
  {mesh : Real}
-- given
  (F : Nat -> Nat -> Complex)
  (i0 j0 width height : Nat)
  (hCR : ∀ a b, a < width + height -> b < width + height -> IsingCellCRAt F (i0 + a) (j0 + b)) :
-- imply
  reflectedRadialAxisStaircaseBoundaryIntegral mesh F i0 j0 width height = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisStaircaseBoundaryIntegral_eq_zero_of_cellCR mesh F i0 j0 width height hCR

/--
[sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary_eq
  {mesh : Real}
-- given
  (F : Nat -> Nat -> Complex)
  (i0 j0 width height : Nat) :
-- imply
  (∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width, reflectedRadialBilinearCellContour mesh (F (i0 + i) (j0 + j)) (F (i0 + i + 1) (j0 + j)) (F (i0 + i) (j0 + j + 1)) (F (i0 + i + 1) (j0 + j + 1))) = reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height := by
-- proof
  apply StatMech.Universality.sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary mesh F i0 j0 width height

/--
[reflectedRadialRectangleBoundaryIntegral_eq_zero_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialRectangleBoundaryIntegral_eq_zero_of_cellCR_eq
  {mesh : Real}
-- given
  (F : Nat -> Nat -> Complex)
  (i0 j0 width height : Nat)
  (hCR : forall i j, i < width -> j < height -> IsingCellCRAt F (i0 + i) (j0 + j)) :
-- imply
  reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialRectangleBoundaryIntegral_eq_zero_of_cellCR mesh F i0 j0 width height hCR

/--
[reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR_eq
  {mesh : Real}
  {cells : Finset (Nat × Nat)}
-- given
  (F : Nat -> Nat -> Complex)
  (hCR : forall p, p ∈ cells -> IsingCellCRAt F p.1 p.2) :
-- imply
  reflectedRadialCellRegionBoundaryIntegral mesh F cells = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialCellRegionBoundaryIntegral_eq_zero_of_cellCR mesh F cells hCR

/--
[fkIsingSquareBoundaryRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero_eq
  {n m : Nat}
  {mesh : Real}
  {cells : Finset (Nat × Nat)}
-- given
  (hn : 0 < n)
  (hm : m <= n)
  (hinterior : forall p, p ∈ cells -> p.1 + 2 < m ∧ p.2 + 2 < m) :
-- imply
  reflectedRadialCellRegionBoundaryIntegral mesh (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm) cells = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero n m hn hm mesh cells hinterior

/--
[fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero_eq
  {n : Nat}
  {mesh : Real}
  {cells : Finset (Nat × Nat)}
-- given
  (hn : 0 < n)
  (hinterior : forall p, p ∈ cells -> p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
-- imply
  reflectedRadialCellRegionBoundaryIntegral mesh (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn) cells = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_reflectedRegionContour_eq_zero n hn mesh cells hinterior

/--
[fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero_eq
  {n : Nat}
  {gridScale normalizationScale : Real}
  {cells : Finset (Nat × Nat)}
-- given
  (hn : 0 < n)
  (hinterior : forall p, p ∈ cells -> p.1 + 2 < 2 * n ∧ p.2 + 2 < 2 * n) :
-- imply
  reflectedRadialCellRegionBoundaryIntegral gridScale (fun i j => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j / (Real.sqrt (2 * normalizationScale) : Complex)) cells = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchNormalizedExtension_reflectedRegionContour_eq_zero n hn gridScale normalizationScale cells hinterior

/--
[fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hi : i + 2 < 2 * n)
  (hj : j + 2 < 2 * n) :
-- imply
  reflectedRadialBilinearCellPathIntegral gridScale (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn (i + 1) j / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i (j + 1) / (Real.sqrt (2 * normalizationScale) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn (i + 1) (j + 1) / (Real.sqrt (2 * normalizationScale) : Complex)) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatch_reflectedCellPathIntegral_eq_zero n i j hn hi hj gridScale normalizationScale

/--
[fkIsingExpandingSquareScale_mul_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_mul_side_eq
  {k : Nat} :
-- imply
  fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k = (k + 1 : Nat) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_mul_side k

/--
[fkIsingExpandingSquareScale_mul_side_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_mul_side_tendsto_atTop_eq :
-- imply
  Tendsto (fun k => fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k) atTop atTop := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_mul_side_tendsto_atTop

/--
[fkIsingExpandingSquareScale_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquareScale_tendsto_zero_eq :
-- imply
  Tendsto fkIsingExpandingSquareScale atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareScale_tendsto_zero

/--
[fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop_eq
  {layers : Real} :
-- imply
  Tendsto (fun k => fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k - layers * fkIsingExpandingSquareScale k) atTop atTop := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquareCenteredInteriorRadius_tendsto_atTop layers

/--
[fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior_eq
  {R layers : Real} :
-- imply
  ∀ᶠ k in atTop, R ≤ fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k - layers * fkIsingExpandingSquareScale k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquare_eventually_fixedRadius_in_centeredInterior R layers

/--
[shiftedRealGridFloor_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma shiftedRealGridFloor_error_eq
  {mesh shift x : Real}
-- given
  (hmesh : 0 < mesh) :
-- imply
  0 ≤ x - shiftedRealGridFloor mesh shift x ∧ x - shiftedRealGridFloor mesh shift x < mesh := by
-- proof
  apply StatMech.Universality.shiftedRealGridFloor_error mesh shift x hmesh

/--
[abs_shiftedRealGridFloor_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma abs_shiftedRealGridFloor_sub_lt_eq
  {mesh shift x : Real}
-- given
  (hmesh : 0 < mesh) :
-- imply
  |shiftedRealGridFloor mesh shift x - x| < mesh := by
-- proof
  apply StatMech.Universality.abs_shiftedRealGridFloor_sub_lt mesh shift x hmesh

/--
[shiftedRealGridFloor_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma shiftedRealGridFloor_mono_eq
  {mesh shift x y : Real}
-- given
  (hmesh : 0 < mesh)
  (hxy : x ≤ y) :
-- imply
  shiftedRealGridFloor mesh shift x ≤ shiftedRealGridFloor mesh shift y := by
-- proof
  apply StatMech.Universality.shiftedRealGridFloor_mono mesh shift x y hmesh hxy

/--
[shiftedRealGridFloor_add_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma shiftedRealGridFloor_add_steps_eq
  {mesh shift x y : Real}
-- given
  (hmesh : 0 < mesh)
  (hxy : x ≤ y) :
-- imply
  shiftedRealGridFloor mesh shift x + (shiftedRealGridFloorSteps mesh shift x y : Real) * mesh = shiftedRealGridFloor mesh shift y := by
-- proof
  apply StatMech.Universality.shiftedRealGridFloor_add_steps mesh shift x y hmesh hxy

/--
[shiftedRealGridFloor_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma shiftedRealGridFloor_tendsto_eq
  {shift x : Real}
-- given
  (mesh : Nat -> Real)
  (hmeshPos : ∀ k, 0 < mesh k)
  (hmesh : Tendsto mesh atTop (nhds 0)) :
-- imply
  Tendsto (fun k => shiftedRealGridFloor (mesh k) shift x) atTop (nhds x) := by
-- proof
  apply StatMech.Universality.shiftedRealGridFloor_tendsto mesh hmeshPos hmesh shift x

/--
[reflectedRadialAxisSnapWidth_mul_mesh_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisSnapWidth_mul_mesh_le_eq
  {mesh : Real}
  {z w : Complex}
-- given
  (hmesh : 0 < mesh)
  (hre : z.re ≤ w.re) :
-- imply
  (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh ≤ w.re - z.re + mesh := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisSnapWidth_mul_mesh_le mesh z w hmesh hre

/--
[reflectedRadialAxisSnapHeight_mul_mesh_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisSnapHeight_mul_mesh_le_eq
  {mesh : Real}
  {z w : Complex}
-- given
  (hmesh : 0 < mesh)
  (him : z.im ≤ w.im) :
-- imply
  (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh ≤ w.im - z.im + mesh := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisSnapHeight_mul_mesh_le mesh z w hmesh him

/--
[reflectedRadialAxisSnap_oppositeCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisSnap_oppositeCorner_eq
  {mesh : Real}
  {z w : Complex}
-- given
  (hmesh : 0 < mesh)
  (hre : z.re ≤ w.re)
  (him : z.im ≤ w.im) :
-- imply
  (shiftedRealGridFloor mesh (1 / 2) z.re + (reflectedRadialAxisSnapWidth mesh z w : Real) * mesh : Real) + (shiftedRealGridFloor mesh 0 z.im + (reflectedRadialAxisSnapHeight mesh z w : Real) * mesh : Real) * Complex.I = reflectedRadialAxisSnap mesh w := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisSnap_oppositeCorner mesh z w hmesh hre him

/--
[reflectedRadialAxisSnap_dist_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisSnap_dist_lt_eq
  {mesh : Real}
  {z : Complex}
-- given
  (hmesh : 0 < mesh) :
-- imply
  dist (reflectedRadialAxisSnap mesh z) z < 2 * mesh := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisSnap_dist_lt mesh z hmesh

/--
[reflectedRadialAxisSnap_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisSnap_tendsto_eq
  {z : Complex}
-- given
  (mesh : Nat -> Real)
  (hmeshPos : ∀ k, 0 < mesh k)
  (hmesh : Tendsto mesh atTop (nhds 0)) :
-- imply
  Tendsto (fun k => reflectedRadialAxisSnap (mesh k) z) atTop (nhds z) := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisSnap_tendsto mesh hmeshPos hmesh z

/--
[reflectedRadialAxisFloor_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialAxisFloor_box_eq
  {n : Nat}
  {mesh x y : Real}
-- given
  (hmesh : 0 < mesh)
  (hinside : |x| + |y| + 3 * mesh ≤ mesh * n) :
-- imply
  0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ ∧ 0 ≤ (n : Int) + ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ ∧ ⌊x / mesh - 1 / 2⌋ - ⌊y / mesh⌋ + 1 < (n : Int) ∧ ⌊x / mesh - 1 / 2⌋ + ⌊y / mesh⌋ + 1 < (n : Int) := by
-- proof
  apply StatMech.Universality.reflectedRadialAxisFloor_box n mesh x y hmesh hinside

/--
[isingReflectedCenteredRadialGridPosition_snap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_snap_eq
  {n : Nat}
  {mesh : Real}
  {z : Complex}
-- given
  (hi : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊z.im / mesh⌋)
  (hj : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (reflectedRadialAxisSnapI n mesh z) (reflectedRadialAxisSnapJ n mesh z) = reflectedRadialAxisSnap mesh z := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_snap n mesh z hi hj

/--
[isingReflectedCenteredRadialGridPosition_axisSnapBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridPosition_axisSnapBase_eq
  {n : Nat}
  {mesh : Real}
  {z w : Complex}
-- given
  (hmesh : 0 < mesh)
  (him : z.im ≤ w.im)
  (hi0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊w.im / mesh⌋)
  (hj0 : 0 ≤ (n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋) :
-- imply
  isingReflectedCenteredRadialGridPosition mesh n (reflectedRadialAxisSnapBaseI n mesh z w + reflectedRadialAxisSnapHeight mesh z w) (reflectedRadialAxisSnapBaseJ n mesh z) = reflectedRadialAxisSnap mesh z := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridPosition_axisSnapBase n mesh z w hmesh him hi0 hj0

/--
[fkIsingExpandingSquare_eventually_axisSnap_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingSquare_eventually_axisSnap_interior_eq
  {z w : Complex}
-- given
  (hre : z.re ≤ w.re)
  (him : z.im ≤ w.im) :
-- imply
  ∀ᶠ k in atTop, 0 ≤ (fkIsingExpandingSquareSide k : Int) + ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ - ⌊w.im / fkIsingExpandingSquareScale k⌋ ∧ 0 ≤ (fkIsingExpandingSquareSide k : Int) + ⌊z.re / fkIsingExpandingSquareScale k - 1 / 2⌋ + ⌊z.im / fkIsingExpandingSquareScale k⌋ ∧ reflectedRadialAxisSnapBaseI (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) z w + reflectedRadialAxisSnapWidth (fkIsingExpandingSquareScale k) z w + reflectedRadialAxisSnapHeight (fkIsingExpandingSquareScale k) z w + 1 < 2 * fkIsingExpandingSquareSide k ∧ reflectedRadialAxisSnapBaseJ (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) z + reflectedRadialAxisSnapWidth (fkIsingExpandingSquareScale k) z w + reflectedRadialAxisSnapHeight (fkIsingExpandingSquareScale k) z w + 1 < 2 * fkIsingExpandingSquareSide k := by
-- proof
  apply StatMech.Universality.fkIsingExpandingSquare_eventually_axisSnap_interior z w hre him

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous_eq
  {k : Nat} :
-- imply
  Continuous (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_continuous k

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n i j) ((gridScale : Complex) / 2 * (1 - Complex.I)) = ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex) + fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i + 1, by omega⟩ ⟨j, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) / 2) * ((gridScale : Complex) / 2 * (1 - Complex.I)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n i j) ((gridScale : Complex) / 2 * (1 + Complex.I)) = ((fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex) + fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn ⟨i, by omega⟩ ⟨j + 1, by omega⟩ / (Real.sqrt (2 * normalizationScale) : Complex)) / 2) * ((gridScale : Complex) / 2 * (1 + Complex.I)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n i j) ((gridScale : Complex) / 2 * (1 - Complex.I)) = reflectedRadialHorizontalEdgeIntegral gridScale (fun a b => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn a b / (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_iEdgeIntegral_eq_edge n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n i j) ((gridScale : Complex) / 2 * (1 + Complex.I)) = reflectedRadialVerticalEdgeIntegral gridScale (fun a b => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn a b / (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_jEdgeIntegral_eq_edge n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n (i + 1) j) (-((gridScale : Complex) / 2 * (1 - Complex.I))) = -reflectedRadialHorizontalEdgeIntegral gridScale (fun a b => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn a b / (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negIEdgeIntegral_eq_edge n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge_eq
  {n i j : Nat}
  {gridScale normalizationScale : Real}
-- given
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i + 1 < 2 * n)
  (hj : j + 1 < 2 * n) :
-- imply
  complexDisplacementIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) (isingReflectedCenteredRadialGridPosition gridScale n i (j + 1)) (-((gridScale : Complex) / 2 * (1 + Complex.I))) = -reflectedRadialVerticalEdgeIntegral gridScale (fun a b => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn a b / (Real.sqrt (2 * normalizationScale) : Complex)) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_negJEdgeIntegral_eq_edge n i j hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary_eq
  {gridScale normalizationScale : Real}
-- given
  (n i0 j0 width height : Nat)
  (hn : 0 < n)
  (hgridScale : gridScale ≠ 0)
  (hi : i0 + width + height + 1 < 2 * n)
  (hj : j0 + width + height + 1 < 2 * n) :
-- imply
  reflectedRadialAxisStaircasePathIntegral (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant n hn gridScale normalizationScale) gridScale n i0 j0 width height = reflectedRadialAxisStaircaseBoundaryIntegral gridScale (fun i j => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j / (Real.sqrt (2 * normalizationScale) : Complex)) i0 j0 width height := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedAxisStaircasePathIntegral_eq_boundary n i0 j0 width height hn gridScale normalizationScale hgridScale hi hj

/--
[fkIsingExpandingBoundarySquareCenteredReflectedRegionContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedRegionContour_eq_zero_eq
  {k : Nat}
  {cells : Finset (Nat × Nat)}
-- given
  (hinterior : forall p, p ∈ cells -> p.1 + 2 < 2 * fkIsingExpandingSquareSide k ∧ p.2 + 2 < 2 * fkIsingExpandingSquareSide k) :
-- imply
  reflectedRadialCellRegionBoundaryIntegral (fkIsingExpandingSquareScale k) (fun i j => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) i j / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) cells = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedRegionContour_eq_zero k cells hinterior

/--
[fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero_eq
-- given
  (k i0 j0 width height : Nat)
  (hi : i0 + width + height + 1 < 2 * fkIsingExpandingSquareSide k)
  (hj : j0 + width + height + 1 < 2 * fkIsingExpandingSquareSide k) :
-- imply
  reflectedRadialAxisStaircaseBoundaryIntegral (fkIsingExpandingSquareScale k) (fun i j => fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) i j / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) i0 j0 width height = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircaseContour_eq_zero k i0 j0 width height hi hj

/--
[fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero_eq
-- given
  (k i0 j0 width height : Nat)
  (hi : i0 + width + height + 1 < 2 * fkIsingExpandingSquareSide k)
  (hj : j0 + width + height + 1 < 2 * fkIsingExpandingSquareSide k) :
-- imply
  reflectedRadialAxisStaircasePathIntegral (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) i0 j0 width height = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedAxisStaircasePathIntegral_eq_zero k i0 j0 width height hi hj

/--
[fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero_eq
  {z w : Complex}
-- given
  (hre : z.re ≤ w.re)
  (him : z.im ≤ w.im) :
-- imply
  ∀ᶠ k in atTop, reflectedRadialAxisStaircasePathIntegral (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k) (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareSide k) (reflectedRadialAxisSnapBaseI (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) z w) (reflectedRadialAxisSnapBaseJ (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareScale k) z) (reflectedRadialAxisSnapWidth (fkIsingExpandingSquareScale k) z w) (reflectedRadialAxisSnapHeight (fkIsingExpandingSquareScale k) z w) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquare_eventually_axisSnapStaircasePathIntegral_eq_zero z w hre him

/--
[fkIsingExpandingBoundarySquareCenteredReflectedCellPathIntegral_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedCellPathIntegral_eq_zero_eq
  {k i j : Nat}
-- given
  (hi : i + 2 < 2 * fkIsingExpandingSquareSide k)
  (hj : j + 2 < 2 * fkIsingExpandingSquareSide k) :
-- imply
  reflectedRadialBilinearCellPathIntegral (fkIsingExpandingSquareScale k) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) i j / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (i + 1) j / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) i (j + 1) / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) (i + 1) (j + 1) / (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedCellPathIntegral_eq_zero k i j hi hj

/--
[reflectedRadialBilinearCellContour_eq_zero_of_IsingCellCRAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflectedRadialBilinearCellContour_eq_zero_of_IsingCellCRAt_eq
  {mesh : Real}
  {i j : Nat}
-- given
  (F : Nat -> Nat -> Complex)
  (hCR : IsingCellCRAt F i j) :
-- imply
  reflectedRadialBilinearCellContour mesh (F i j) (F (i + 1) j) (F i (j + 1)) (F (i + 1) (j + 1)) = 0 := by
-- proof
  apply StatMech.Universality.reflectedRadialBilinearCellContour_eq_zero_of_IsingCellCRAt mesh F i j hCR

/--
[BoundaryRadialTensorTentGeometry.subsequentialMorera_of_contourError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma subsequentialMorera_of_contourError_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {H : BoundaryRadialTensorTentGeometry.VanishingRectangleContourError A G}
-- given
  (hU : A.U = Set.univ) :
-- imply
  forall (phi psi : Nat -> Nat) (f : Complex -> Complex), StrictMono phi -> StrictMono psi -> TendstoLocallyUniformlyOn (fun n => BoundaryRadialTensorTentGeometry.interpolant A G (phi (psi n))) f atTop A.U -> Complex.IsConservativeOn f A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.subsequentialMorera_of_contourError A hU G H

/--
[BoundaryRadialTensorTentGeometry.reflected_subsequentialMorera_of_contourError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean)
-/
@[path]
private lemma reflected_subsequentialMorera_of_contourError_eq
  {A : FKIsingCaratheodoryApproximation}
  {G : BoundaryRadialTensorTentGeometry A}
  {H : BoundaryRadialTensorTentGeometry.ReflectedVanishingRectangleContourError A G}
-- given
  (hU : A.reflect.U = Set.univ) :
-- imply
  forall (phi psi : Nat -> Nat) (f : Complex -> Complex), StrictMono phi -> StrictMono psi -> TendstoLocallyUniformlyOn (fun n => BoundaryRadialTensorTentGeometry.reflectedInterpolant A G (phi (psi n))) f atTop A.reflect.U -> Complex.IsConservativeOn f A.reflect.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.BoundaryRadialTensorTentGeometry.reflected_subsequentialMorera_of_contourError A hU G H


-- created on 2026-10-23
