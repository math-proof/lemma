import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
open Real MeasureTheory MeasureTheory.Measure TestFunctions FourierInversion SobolevSpace
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap
open FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap
open TestFunctions


namespace FourierInversion

/--
[fourier_schwartz_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma fourier_schwartz_isomorphism
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [NormedAddCommGroup E]
  [NormedSpace ℂ E]
  [CompleteSpace E] :
-- imply
  ∃ e : 𝓢(V, E) ≃L[ℂ] 𝓢(V, E), (∀ f, e f = 𝓕 f) ∧ (∀ f, e.symm f = 𝓕⁻ f) := by
-- proof
  exact ⟨FourierTransform.fourierCLE ℂ 𝓢(V, E),
    fun f => FourierTransform.fourierCLE_apply f,
    fun f => FourierTransform.fourierCLE_symm_apply f⟩

end FourierInversion

namespace FourierInversion

/--
[fourierSchwartzCLE_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma fourierSchwartzCLE_apply
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [NormedAddCommGroup E]
  [NormedSpace ℂ E]
  [CompleteSpace E]
  {f : 𝓢(V, E)} :
-- imply
  fourierSchwartzCLE f = 𝓕 f :=
-- proof
  rfl

end FourierInversion

namespace FourierInversion

/--
[fourierSchwartzCLE_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma fourierSchwartzCLE_symm_apply
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  [NormedAddCommGroup E]
  [NormedSpace ℂ E]
  [CompleteSpace E]
  {f : 𝓢(V, E)} :
-- imply
  fourierSchwartzCLE.symm f = 𝓕⁻ f :=
-- proof
  rfl

end FourierInversion

namespace FourierInversion

/--
[parseval_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma parseval_identity
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {φ ψ : SchwartzMap V ℂ} :
-- imply
  ∫ x, φ x * starRingEnd ℂ (ψ x) = ∫ ξ, 𝓕 φ ξ * starRingEnd ℂ (𝓕 ψ ξ) := by
-- proof
  have key : ∀ (f g : SchwartzMap V ℂ) (x : V),
    f x * starRingEnd ℂ (g x) = @inner ℂ ℂ _ (g x) (f x) := fun f g x => by
    simp [inner]
  simp_rw [key]
  exact (SchwartzMap.integral_inner_fourier_fourier ψ φ).symm
section TemperedDistributionIsomorphism
open FourierTransform TemperedDistribution LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end FourierInversion

namespace FourierInversion

/--
[fourier_iterDerivCoord_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma fourier_iterDerivCoord_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  𝓕 (iterDistribDerivCoord j k u) = iterCoordMulFourier j k (𝓕 u) := by
-- proof
  induction k generalizing u with
  | zero => simp [iterDistribDerivCoord, iterCoordMulFourier]
  | succ k ih =>
    simp only [iterDistribDerivCoord, iterCoordMulFourier, Function.iterate_succ', Function.comp]
    rw [TemperedDistribution.fourier_lineDerivOp_eq]
    congr 1; congr 1
    exact ih u

end FourierInversion

namespace FourierInversion

/--
[fourier_iterDeriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma fourier_iterDeriv_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {n : ℕ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  𝓕 (iterDistribDeriv α u) = iterMulFourier α (𝓕 u) := by
-- proof
  unfold iterDistribDeriv iterMulFourier
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [fourier_iterDerivCoord_eq]
    congr 1

end FourierInversion

namespace FourierInversion

/--
[iterDerivCoord_fourier_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma iterDerivCoord_fourier_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {n : ℕ}
  {j : Fin n}
  {k : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iterDistribDerivCoord j k (𝓕 u) = 𝓕 (iterCoordNegMulDistrib j k u) := by
-- proof
  induction k generalizing u with
  | zero => simp [iterDistribDerivCoord, iterCoordNegMulDistrib]
  | succ k ih =>
    simp only [iterDistribDerivCoord, iterCoordNegMulDistrib, Function.iterate_succ',
      Function.comp]
    show ∂_{EuclideanSpace.single j (1 : ℝ)} (iterDistribDerivCoord j k (𝓕 u)) =
      𝓕 (-(2 * ↑Real.pi * Complex.I) •
        smulLeftCLM ℂ (fun x => ↑(@inner ℝ _ _ x (EuclideanSpace.single j 1)))
        (iterCoordNegMulDistrib j k u))
    rw [ih]
    exact TemperedDistribution.lineDerivOp_fourier_eq _ _
end FourierInversion
open scoped SchwartzMap
open TestFunctions


namespace SobolevSpace

/--
[sobolevWeight_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma sobolevWeight_ne_zero
  {n : ℕ}
  {s : ℝ}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  sobolevWeight n s ξ ≠ 0 :=
-- proof
  ne_of_gt (sobolevWeight_pos n s ξ)

end SobolevSpace

namespace SobolevSpace

/--
[memHs_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma memHs_of_le
  {n : ℕ}
  {n : ℕ}
  {s t : ℝ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hst : t ≤ s)
  (hu : MemHs n s u) :
-- imply
  MemHs n t u := by
-- proof
  obtain ⟨g, hg_mem, hg_eq⟩ := hu
  refine ⟨fun ξ => (sobolevWeight n (t - s) ξ : ℂ) * g ξ, ?_, ?_⟩
  ·
    have hweight_le_one : ∀ ξ : EuclideanSpace ℝ (Fin n),
      sobolevWeight n (t - s) ξ ≤ 1 := by
      intro ξ
      simp only [sobolevWeight, japaneseBracket]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (Real.one_le_sqrt.mpr (by linarith [sq_nonneg (‖ξ‖ : ℝ)]))
        (by linarith)
    have hweight_nonneg : ∀ ξ : EuclideanSpace ℝ (Fin n),
      0 ≤ sobolevWeight n (t - s) ξ :=
      fun ξ => le_of_lt (sobolevWeight_pos n (t - s) ξ)
    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖(sobolevWeight n (t - s) ξ : ℂ) * g ξ‖ ≤ 1 * ‖g ξ‖ := by
      intro ξ
      rw [norm_mul, one_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [Complex.norm_real, Real.norm_of_nonneg (hweight_nonneg ξ)]
      exact hweight_le_one ξ
    have hweight_cont : Continuous (fun ξ : EuclideanSpace ℝ (Fin n) =>
      (sobolevWeight n (t - s) ξ : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      show Continuous (fun ξ => japaneseBracket n ξ ^ (t - s))
      apply Continuous.rpow_const
      · exact continuous_sqrt.comp (by continuity)
      · intro ξ; exact Or.inl (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hweight_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)
  ·
    intro φ
    rw [hg_eq φ]
    congr 1
    ext ξ
    have hjb_pos : (0 : ℝ) < japaneseBracket n ξ := japaneseBracket_pos n ξ
    have hkey : (sobolevWeight n t ξ : ℂ)⁻¹ * (sobolevWeight n (t - s) ξ : ℂ) =
      (sobolevWeight n s ξ : ℂ)⁻¹ := by
      simp only [sobolevWeight]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
      congr 1
      have h1 : (japaneseBracket n ξ ^ t)⁻¹ = japaneseBracket n ξ ^ (-t) :=
        (Real.rpow_neg hjb_pos.le t).symm
      have h2 : (japaneseBracket n ξ ^ s)⁻¹ = japaneseBracket n ξ ^ (-s) :=
        (Real.rpow_neg hjb_pos.le s).symm
      rw [h1, h2, ← Real.rpow_add hjb_pos]
      congr 1
      linarith
    rw [← hkey]; ring

end SobolevSpace

namespace SobolevSpace

/--
[Hs.instCompleteSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma Hs.instCompleteSpace
  {n : ℕ}
  {s : ℝ} :
-- imply
  CompleteSpace (Hs n s) :=
-- proof
  (completeSpace_congr (Isometry.of_dist_eq (fun _ _ => rfl)).isUniformEmbedding
    (e := Hs.equivLp n s)).mpr inferInstance
attribute [instance] Hs.instCompleteSpace

end SobolevSpace

namespace SobolevSpace

/--
[schwartz_dense_in_Hs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma schwartz_dense_in_Hs
  {n : ℕ}
  {s : ℝ}
  [NormedAddCommGroup (Hs n s)]
  [NormedSpace ℝ (Hs n s)]
  [NormedSpace ℂ (Hs n s)]
  {Φ : Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))} :
-- imply
  DenseRange (Φ.symm ∘ (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
-- proof
  DenseRange.comp
    ((EquivLike.surjective Φ.symm).denseRange)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (LinearIsometryEquiv.continuous Φ.symm)

end SobolevSpace

namespace SobolevSpace

/--
[dualIdentification_norm_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma dualIdentification_norm_map
  {n : ℕ}
  {s : ℝ}
  {u' : Hs n (-s)} :
-- imply
  ‖dualIdentification n s u'‖ = ‖u'‖ :=
-- proof
  (dualIdentification n s).norm_map u'

end SobolevSpace

namespace SobolevSpace

/--
[dualIdentification_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma dualIdentification_bijective
  {n : ℕ}
  {s : ℝ} :
-- imply
  Function.Bijective (dualIdentification n s) :=
-- proof
  (dualIdentification n s).bijective

end SobolevSpace

namespace SobolevSpace

/--
[proposition_9_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma proposition_9_8
  {n : ℕ}
  {s : ℝ} :
-- imply
  (∃ Φ : Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))), DenseRange (Φ.symm ∘ (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))))) ∧ Nonempty (Hs n (-s) ≃ₗᵢ⋆[ℂ] (Hs n s →L[ℂ] ℂ)) := by
-- proof
  constructor
  · exact ⟨fourierWeightEquiv n s,
    schwartz_dense_in_Hs n s (fourierWeightEquiv n s)⟩
  · exact ⟨dualIdentification n s⟩

end SobolevSpace

namespace SobolevSpace

/--
[sobolevWeight_complex_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma sobolevWeight_complex_hasTemperateGrowth
  {n : ℕ}
  {s : ℝ} :
-- imply
  (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)).HasTemperateGrowth := by
-- proof
  have hreal : (fun ξ : EuclideanSpace ℝ (Fin n) =>
    sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
      (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring
  exact Function.Complex.hasTemperateGrowth_ofReal.comp hreal

end SobolevSpace

namespace SobolevSpace

/--
[schwartz_memHs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma schwartz_memHs
  {n : ℕ}
  {s : ℝ}
  {f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  MemHs n s (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
-- proof
  set weight : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (sobolevWeight n s ξ : ℂ)
  have htemp : weight.HasTemperateGrowth := sobolevWeight_complex_hasTemperateGrowth n s
  set h : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) := SchwartzMap.smulLeftCLM ℂ weight (𝓕 f)
  refine ⟨fun ξ => h ξ, h.memLp 2, fun φ => ?_⟩
  have key : ∀ ξ : EuclideanSpace ℝ (Fin n),
    (sobolevWeight n s ξ : ℂ)⁻¹ * h ξ * φ ξ = (𝓕 f) ξ * φ ξ := fun ξ => by
    have hval : h ξ = (sobolevWeight n s ξ : ℂ) * (𝓕 f) ξ := by
      have := SchwartzMap.smulLeftCLM_apply_apply htemp (𝓕 f) ξ
      simp only [smul_eq_mul] at this
      exact this
    rw [hval]
    have hne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sobolevWeight_ne_zero n s ξ)
    field_simp
  simp_rw [key]
  rw [TemperedDistribution.fourier_apply, SchwartzMap.coe_apply]
  rw [SchwartzMap.integral_fourier_mul_eq f φ]
  congr 1
  ext x
  simp [smul_eq_mul, mul_comm]

end SobolevSpace

namespace SobolevSpace

/--
[one_le_japaneseBracket](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma one_le_japaneseBracket
  {n : ℕ}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  1 ≤ japaneseBracket n ξ := by
-- proof
  unfold japaneseBracket
  rw [Real.le_sqrt (by linarith) (by positivity)]
  nlinarith [sq_nonneg ‖ξ‖]

end SobolevSpace

namespace SobolevSpace

/--
[abs_coord_le_japaneseBracket](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma abs_coord_le_japaneseBracket
  {n : ℕ}
  {ξ : EuclideanSpace ℝ (Fin n)}
  {i : Fin n} :
-- imply
  |ξ i| ≤ japaneseBracket n ξ := by
-- proof
  unfold japaneseBracket
  have h1 : |ξ i| ≤ ‖ξ‖ := by
    have h_sq : |ξ i| ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc |ξ i| ^ 2 = ‖(ξ.ofLp i : ℝ)‖ ^ 2 := by rw [Real.norm_eq_abs]
        _ ≤ ∑ j, ‖ξ.ofLp j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖ξ.ofLp j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg _)).2
  calc |ξ i| ≤ ‖ξ‖ := h1
    _ ≤ sqrt (1 + ‖ξ‖ ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
      nlinarith [sq_nonneg ‖ξ‖]

end SobolevSpace

namespace SobolevSpace

/--
[monomial_sobolevWeight_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma monomial_sobolevWeight_norm_le_one
  {n : ℕ}
  {n : ℕ}
  {m : ℕ}
  {α : Fin n → ℕ}
  {ξ : EuclideanSpace ℝ (Fin n)}
-- given
  (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m) :
-- imply
  ‖SchwartzRepresentation.monomial α ξ * (sobolevWeight n (-(m : ℝ)) ξ : ℂ)‖ ≤ 1 := by
-- proof
  have hα_ord : SchwartzRepresentation.multiIndexOrder α ≤ m :=
    SchwartzRepresentation.mem_multiIndicesBall_iff.mp hα
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hjb_pos : 0 < japaneseBracket n ξ := japaneseBracket_pos n ξ
  have hjb_ge : 1 ≤ japaneseBracket n ξ := one_le_japaneseBracket n ξ
  have hsw_pos : 0 < sobolevWeight n (-(m : ℝ)) ξ := sobolevWeight_pos n _ ξ
  rw [abs_of_pos hsw_pos]
  unfold SchwartzRepresentation.monomial
  rw [norm_prod]
  simp_rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h_prod : ∏ i : Fin n, |ξ i| ^ (α i) ≤ (japaneseBracket n ξ) ^ (∑ i, α i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod
    · intro i _; exact pow_nonneg (abs_nonneg _) _
    · intro i _; exact pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le_japaneseBracket n ξ i) _
  unfold sobolevWeight
  calc (∏ i : Fin n, |ξ i| ^ α i) * japaneseBracket n ξ ^ (-(m : ℝ))
    ≤ japaneseBracket n ξ ^ (∑ i, α i) * japaneseBracket n ξ ^ (-(m : ℝ)) := by
      apply mul_le_mul_of_nonneg_right h_prod (le_of_lt (Real.rpow_pos_of_pos hjb_pos _))
    _ = japaneseBracket n ξ ^ ((↑(∑ i : Fin n, α i) : ℝ) + (-(m : ℝ))) := by
      rw [← Real.rpow_natCast (japaneseBracket n ξ) (∑ i, α i),
        ← Real.rpow_add hjb_pos]
    _ ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hjb_ge
      have : (SchwartzRepresentation.multiIndexOrder α : ℝ) ≤ (m : ℝ) :=
        Nat.cast_le.mpr hα_ord
      simp only [SchwartzRepresentation.multiIndexOrder] at this
      linarith

end SobolevSpace

namespace SobolevSpace

/--
[monomial_sobolev_weight_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma monomial_sobolev_weight_bound
  {n : ℕ}
  {m : ℕ}
  {α : Fin n → ℕ}
  {ξ : EuclideanSpace ℝ (Fin n)}
-- given
  (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m) :
-- imply
  ‖(∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) * (sobolevWeight n (-(m : ℝ)) ξ : ℂ)‖ ≤ 1 :=
-- proof
  monomial_sobolevWeight_norm_le_one m α hα ξ

end SobolevSpace

namespace SobolevSpace

/--
[memLp_mul_of_bound_one_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma memLp_mul_of_bound_one_backward
  {n : ℕ}
-- given
  (h g : EuclideanSpace ℝ (Fin n) → ℂ)
  (hh_meas : AEStronglyMeasurable h (volume : Measure (EuclideanSpace ℝ (Fin n))))
  (hh : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖h x‖ ≤ 1)
  (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
-- imply
  MemLp (fun x => h x * g x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply MemLp.of_le_mul hg (hh_meas.mul hg.aestronglyMeasurable)
  filter_upwards [hh] with x hx
  calc ‖h x * g x‖ = ‖h x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ 1 * ‖g x‖ := by gcongr

end SobolevSpace

namespace SobolevSpace

/--
[hasTemperateGrowth_prod'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma hasTemperateGrowth_prod'
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedCommRing R]
  [NormedAlgebra ℝ R]
  [DecidableEq ι]
  {s : Finset ι}
  {f : ι → E → R}
-- given
  (hf : ∀ i ∈ s, Function.HasTemperateGrowth (f i)) :
-- imply
  Function.HasTemperateGrowth (fun x => ∏ i ∈ s, f i x) := by
-- proof
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const 1
  | @insert a s' has' ih =>
    have hconv : (fun x => ∏ i ∈ Insert.insert a s', f i x) =
      (fun x => f a x * ∏ i ∈ s', f i x) := by
      ext x; exact Finset.prod_insert has'
    rw [hconv]
    exact (hf a (Finset.mem_insert_self a s')).mul
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end SobolevSpace

namespace SobolevSpace

/--
[monomial_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma monomial_hasTemperateGrowth
  {n : ℕ}
  {α : Fin n → ℕ} :
-- imply
  Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) => ∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) :=
-- proof
  hasTemperateGrowth_prod' _ _ (fun i _ =>
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth).pow (α i))

end SobolevSpace

namespace SobolevSpace

/--
[memLp_monomial_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma memLp_monomial_mul
  {n : ℕ}
  {m : ℕ}
  {α : Fin n → ℕ}
  {f : EuclideanSpace ℝ (Fin n) → ℂ}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hα : α ∈ SchwartzRepresentation.multiIndicesBall n m)
  (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
-- imply
  MeasureTheory.Integrable (fun ξ => (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) * f ξ * φ ξ) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  let monφ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    SchwartzMap.bilinLeftCLM (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ).flip
      (monomial_hasTemperateGrowth n α) φ
  suffices h : MeasureTheory.Integrable (fun ξ => f ξ * monφ ξ) MeasureTheory.volume from
    h.congr (by filter_upwards with ξ; simp only [monφ,
      SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply']; ring)
  exact hf.integrable_mul (monφ.memLp 2)

end SobolevSpace

namespace SobolevSpace

/--
[mul_conj_div_norm_eq_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma mul_conj_div_norm_eq_norm
  {n : ℕ}
  {z : ℂ} :
-- imply
  z * (starRingEnd ℂ z / (↑‖z‖ : ℂ)) = ↑‖z‖ := by
-- proof
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [div_eq_mul_inv, ← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, sq, mul_assoc, mul_inv_cancel₀ hn, mul_one]

end SobolevSpace

namespace SobolevSpace

/--
[memLp_mul_of_bound_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma memLp_mul_of_bound_one
  {n : ℕ}
-- given
  (h g : EuclideanSpace ℝ (Fin n) → ℂ)
  (hh : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖h x‖ ≤ 1)
  (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
  (hh_meas : AEStronglyMeasurable h (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
-- imply
  MemLp (fun x => h x * g x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply MemLp.of_le_mul hg (hh_meas.mul hg.aestronglyMeasurable)
  filter_upwards [hh] with x hx
  calc ‖h x * g x‖ = ‖h x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ 1 * ‖g x‖ := by gcongr

end SobolevSpace

namespace SobolevSpace

/--
[sgn_denom_algebraic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
lemma sgn_denom_algebraic_identity
  {n : ℕ}
  {m : ℕ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
  {v : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hv_def : ∀ α ξ, v α ξ = (starRingEnd ℂ (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) / (↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ : ℂ)) * (↑(∑ β ∈ SchwartzRepresentation.multiIndicesBall n m, ‖∏ i : Fin n, ((ξ i : ℂ) ^ (β i))‖) : ℂ)⁻¹ * (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹ * g ξ) :
-- imply
  ∀ ξ : EuclideanSpace ℝ (Fin n), ∑ α ∈ SchwartzRepresentation.multiIndicesBall n m, (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) * v α ξ = (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹ * g ξ := by
-- proof
  intro ξ
  simp_rw [hv_def]
  set W := (sobolevWeight n (-(m : ℝ)) ξ : ℂ)⁻¹
  set S := (↑(∑ β ∈ SchwartzRepresentation.multiIndicesBall n m,
    ‖∏ i : Fin n, ((ξ i : ℂ) ^ (β i))‖) : ℂ) with hS_def
  have hS_ne : S ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr; apply ne_of_gt
    calc (0 : ℝ) < 1 := one_pos
      _ = ‖∏ i : Fin n, ((ξ i : ℂ) ^ ((0 : Fin n → ℕ) i))‖ := by simp
      _ ≤ ∑ β ∈ SchwartzRepresentation.multiIndicesBall n m,
        ‖∏ i, ((ξ i : ℂ) ^ (β i))‖ :=
        Finset.single_le_sum (f := fun β => ‖∏ i, ((ξ i : ℂ) ^ (β i))‖)
          (fun _ _ => norm_nonneg _)
          (SchwartzRepresentation.zero_mem_multiIndicesBall n m)
  have step : ∀ α ∈ SchwartzRepresentation.multiIndicesBall n m,
    (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) *
      ((starRingEnd ℂ (∏ i : Fin n, ((ξ i : ℂ) ^ (α i))) /
        (↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ : ℂ)) * S⁻¹ * W * (g ξ)) =
      ↑‖∏ i : Fin n, ((ξ i : ℂ) ^ (α i))‖ * S⁻¹ * W * (g ξ) := by
    intro α _
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
      mul_conj_div_norm_eq_norm (∏ i : Fin n, ((ξ i : ℂ) ^ (α i)))]
  rw [Finset.sum_congr rfl step]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Complex.ofReal_sum, hS_def, mul_inv_cancel₀ hS_ne, one_mul]
/-- Converse direction of Proposition 9.7 of Melrose: every distribution
`u ∈ H^{-m}` admits a representation as a finite sum
`u = ∑_{|α| ≤ m} ∂^α v_α` with each `v_α ∈ L²`. The proof constructs an
explicit `v_α` from the Fourier witness using the polar-decomposition
identity. -/
end SobolevSpace


/--
[fourier_inverse_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma fourier_inverse_left_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(E, F)} :
-- imply
  𝓕⁻ (𝓕 u) = u := by
-- proof
  apply FourierInversion.fourier_inverse_left u

/--
[fourier_inverse_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma fourier_inverse_right_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(E, F)} :
-- imply
  𝓕 (𝓕⁻ u) = u := by
-- proof
  apply FourierInversion.fourier_inverse_right u

/--
[sobolevWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma sobolevWeight_pos_eq
  {n : ℕ}
  {s : ℝ}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  0 < sobolevWeight n s ξ := by
-- proof
  apply SobolevSpace.sobolevWeight_pos n s ξ

/--
[Hs.witnessFunc_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma witnessFunc_memLp_eq
  {n : ℕ}
  {s : ℝ}
  {u : Hs n s} :
-- imply
  MemLp (Hs.witnessFunc n s u) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  apply SobolevSpace.Hs.witnessFunc_memLp n s u

/--
[Hs.witnessFunc_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma witnessFunc_spec_eq
  {n : ℕ}
  {s : ℝ}
  {u : Hs n s} :
-- imply
  ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ := by
-- proof
  apply SobolevSpace.Hs.witnessFunc_spec n s u

/--
[Hs.fromL2_witnessL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma fromL2_witnessL2_eq
  {n : ℕ}
  {s : ℝ}
  {f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))} :
-- imply
  Hs.witnessL2 n s (Hs.fromL2 n s f) = f := by
-- proof
  apply SobolevSpace.Hs.fromL2_witnessL2 n s f

/--
[Hs.witnessL2_fromL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma witnessL2_fromL2_eq
  {n : ℕ}
  {s : ℝ}
  {u : Hs n s} :
-- imply
  Hs.fromL2 n s (Hs.witnessL2 n s u) = u := by
-- proof
  apply SobolevSpace.Hs.witnessL2_fromL2 n s u

/--
[Hs.norm_witnessL2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma norm_witnessL2_eq
  {n : ℕ}
  {s : ℝ}
  {u : Hs n s} :
-- imply
  ‖u‖ = ‖Hs.witnessL2 n s u‖ := by
-- proof
  apply SobolevSpace.Hs.norm_witnessL2 n s u

/--
[Hs.witnessL2_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma witnessL2_add_eq
  {n : ℕ}
  {s : ℝ}
  {u v : Hs n s} :
-- imply
  Hs.witnessL2 n s (u + v) = Hs.witnessL2 n s u + Hs.witnessL2 n s v := by
-- proof
  apply SobolevSpace.Hs.witnessL2_add n s u v

/--
[Hs.witnessL2_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean)
-/
@[path]
private lemma witnessL2_smul_eq
  {n : ℕ}
  {s : ℝ}
  {c : ℂ}
  {u : Hs n s} :
-- imply
  Hs.witnessL2 n s (c • u) = c • Hs.witnessL2 n s u := by
-- proof
  apply SobolevSpace.Hs.witnessL2_smul n s c u


-- created on 2026-10-23
