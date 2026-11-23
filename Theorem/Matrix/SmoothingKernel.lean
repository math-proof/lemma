module

public import Theorem.Matrix.CubicInduction_Carrier
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public noncomputable section

set_option autoImplicit false

section Vocabulary

open NumberField IsDedekindDomain MeasureTheory LanglandsTunnell.CubicInduction
open scoped Matrix

noncomputable section

open scoped Classical

namespace AutomorphicForm

variable (ι : Type) [Fintype ι] [DecidableEq ι]

section TransposeInverse

variable {R : Type*} [CommRing R]


public theorem coe_transposeInvN (g : GL ι R) :
    ((transposeInvN ι g : GL ι R) : Matrix ι ι R) = ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ :=
  rfl


public theorem coe_inv_transposeInvN (g : GL ι R) :
    (((transposeInvN ι g)⁻¹ : GL ι R) : Matrix ι ι R) = ((g : GL ι R) : Matrix ι ι R)ᵀ :=
  rfl


public theorem transposeInvN_transposeInvN (g : GL ι R) : transposeInvN ι (transposeInvN ι g) = g :=
  Units.ext (by rw [coe_transposeInvN, coe_inv_transposeInvN, Matrix.transpose_transpose])


public theorem transposeInvN_mul (g h : GL ι R) :
    transposeInvN ι (g * h) = transposeInvN ι g * transposeInvN ι h :=
  Units.ext (by simp only [Units.val_mul, coe_transposeInvN, mul_inv_rev, Matrix.transpose_mul])

end TransposeInverse

section Kernels

variable (F : Type) [Field F]


public theorem archEntriesN_apply (g : GL ι (InfiniteAdeleRing F)) (i j : ι) :
    archEntriesN ι F g i j =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((g : Matrix ι ι (InfiniteAdeleRing F)) i j) :=
  rfl


public theorem isLeftOrthFiniteN_zero : IsLeftOrthFiniteN ι F (fun _ => 0) :=
  ⟨∅, fun _ _ => Submodule.zero_mem _⟩

variable [NumberField F]


public theorem isArchTestFactorN_zero : IsArchTestFactorN ι F (fun _ => 0) :=
  ⟨⟨fun _ => 0, contDiff_const, fun _ => rfl⟩, HasCompactSupport.zero⟩


public theorem isSmoothingKernelN_zero : IsSmoothingKernelN ι F (fun _ => 0) :=
  ⟨isArchTestFactorN_zero ι F, isLeftOrthFiniteN_zero ι F⟩

end Kernels

section Inclusion

variable (F : Type) [Field F] [NumberField F]


public theorem adeleArch_archMatrixInclN (M : Matrix ι ι (InfiniteAdeleRing F)) (i j : ι) :
    AdelicLevel.adeleArch (𝓞 F) F (archMatrixInclN ι F M i j) = M i j :=
  rfl

omit [Fintype ι] in

public theorem adeleFin_archMatrixInclN (M : Matrix ι ι (InfiniteAdeleRing F)) (i j : ι) :
    AdelicLevel.adeleFin (𝓞 F) F (archMatrixInclN ι F M i j) = (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) i j :=
  rfl

omit [Fintype ι] in

public theorem archMatrixInclN_one : archMatrixInclN ι F (1 : Matrix ι ι (InfiniteAdeleRing F)) = 1 := by
  ext i j
  refine Prod.ext ?_ ?_
  · change (1 : Matrix ι ι (InfiniteAdeleRing F)) i j =
      AdelicLevel.adeleArch (𝓞 F) F ((1 : Matrix ι ι (AdeleRing (𝓞 F) F)) i j)
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · change (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) i j =
      AdelicLevel.adeleFin (𝓞 F) F ((1 : Matrix ι ι (AdeleRing (𝓞 F) F)) i j)
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]


public theorem archMatrixInclN_mul (M N : Matrix ι ι (InfiniteAdeleRing F)) :
    archMatrixInclN ι F (M * N) = archMatrixInclN ι F M * archMatrixInclN ι F N := by
  ext i j
  refine Prod.ext ?_ ?_
  · change (M * N) i j = AdelicLevel.adeleArch (𝓞 F) F ((archMatrixInclN ι F M * archMatrixInclN ι F N) i j)
    simp only [Matrix.mul_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, adeleArch_archMatrixInclN, adeleArch_archMatrixInclN]
  · change (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) i j =
      AdelicLevel.adeleFin (𝓞 F) F ((archMatrixInclN ι F M * archMatrixInclN ι F N) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, adeleFin_archMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.one_mul]


public theorem archComponentN_archInclN (h : GL ι (InfiniteAdeleRing F)) :
    archComponentN ι (𝓞 F) F (archInclN ι F h) = h := by
  ext i j
  rfl


public theorem componentAtN_archInclN (v : HeightOneSpectrum (𝓞 F)) (h : GL ι (InfiniteAdeleRing F)) :
    componentAtN ι (𝓞 F) F v (archInclN ι F h) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change AdelicLevel.finAdeleEval (𝓞 F) F v
      (AdelicLevel.adeleFin (𝓞 F) F (archMatrixInclN ι F (h : Matrix ι ι (InfiniteAdeleRing F)) i j)) =
    (1 : Matrix ι ι (v.adicCompletion F)) i j
  rw [adeleFin_archMatrixInclN]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]


public theorem archComponentN_mul_archInclN (g : GL ι (AdeleRing (𝓞 F) F)) (h : GL ι (InfiniteAdeleRing F)) :
    archComponentN ι (𝓞 F) F (g * archInclN ι F h) = archComponentN ι (𝓞 F) F g * h := by
  rw [map_mul, archComponentN_archInclN]


public theorem componentAtN_mul_archInclN (v : HeightOneSpectrum (𝓞 F)) (g : GL ι (AdeleRing (𝓞 F) F))
    (h : GL ι (InfiniteAdeleRing F)) :
    componentAtN ι (𝓞 F) F v (g * archInclN ι F h) = componentAtN ι (𝓞 F) F v g := by
  rw [map_mul, componentAtN_archInclN, mul_one]

end Inclusion

section Haar

variable (F : Type) [Field F] [NumberField F]


public theorem borelSpace_archGLBorelN : @BorelSpace (GL ι (InfiniteAdeleRing F)) _ (archGLBorelN ι F) :=
  @BorelSpace.mk _ _ (archGLBorelN ι F) rfl


public theorem locallyCompactSpace_archGLN : LocallyCompactSpace (GL ι (InfiniteAdeleRing F)) := by
  haveI : LocallyCompactSpace (Matrix ι ι (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (ι → ι → InfiniteAdeleRing F))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace


public theorem isHaarMeasure_archGLHaarN :
    @Measure.IsHaarMeasure (GL ι (InfiniteAdeleRing F)) _ _ (archGLBorelN ι F) (archGLHaarN ι F) := by
  letI := archGLBorelN ι F
  haveI := borelSpace_archGLBorelN ι F
  haveI : T2Space (Matrix ι ι (InfiniteAdeleRing F)) := inferInstanceAs (T2Space (ι → ι → InfiniteAdeleRing F))
  haveI := locallyCompactSpace_archGLN ι F
  unfold archGLHaarN
  infer_instance

end Haar

section Convolution

variable (F : Type) [Field F] [NumberField F]


public theorem convN_apply (Ψ α : GL ι (InfiniteAdeleRing F) → ℂ) (x : GL ι (InfiniteAdeleRing F)) :
    convN ι F Ψ α x = (letI := archGLBorelN ι F; ∫ h, Ψ (x * h) * α h ∂(archGLHaarN ι F)) :=
  rfl


public theorem archConvN_apply (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (α : GL ι (InfiniteAdeleRing F) → ℂ)
    (g : GL ι (AdeleRing (𝓞 F) F)) :
    archConvN ι F Φ α g = (letI := archGLBorelN ι F; ∫ h, Φ (g * archInclN ι F h) * α h ∂(archGLHaarN ι F)) :=
  rfl


public theorem convN_zero_left (α : GL ι (InfiniteAdeleRing F) → ℂ) : convN ι F (fun _ => 0) α = fun _ => 0 := by
  funext x
  simp [convN]


public theorem convN_zero_right (Ψ : GL ι (InfiniteAdeleRing F) → ℂ) : convN ι F Ψ (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [convN]


public theorem archConvN_zero_left (α : GL ι (InfiniteAdeleRing F) → ℂ) :
    archConvN ι F (fun _ => 0) α = fun _ => 0 := by
  funext g
  simp [archConvN]


public theorem archConvN_zero_right (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) :
    archConvN ι F Φ (fun _ => 0) = fun _ => 0 := by
  funext g
  simp [archConvN]


public theorem archConvN_comp_mul_left (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (α : GL ι (InfiniteAdeleRing F) → ℂ)
    (a g : GL ι (AdeleRing (𝓞 F) F)) :
    archConvN ι F (fun x => Φ (a * x)) α g = archConvN ι F Φ α (a * g) := by
  simp only [archConvN, mul_assoc]


public theorem convN_mul_right (Ψ α : GL ι (InfiniteAdeleRing F) → ℂ) (x k : GL ι (InfiniteAdeleRing F)) :
    convN ι F Ψ α (x * k) = convN ι F Ψ (fun h => α (k⁻¹ * h)) x := by
  simp only [convN]
  letI := archGLBorelN ι F
  haveI := borelSpace_archGLBorelN ι F
  haveI := isHaarMeasure_archGLHaarN ι F
  rw [← integral_mul_left_eq_self (fun h => Ψ (x * h) * α (k⁻¹ * h)) k]
  simp only [mul_assoc, inv_mul_cancel_left]


public theorem archConvN_eq_convN_mul (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (α Ψ : GL ι (InfiniteAdeleRing F) → ℂ)
    (B : GL ι (AdeleRing (𝓞 F) F) → ℂ) (hΦ : ∀ g, Φ g = Ψ (archComponentN ι (𝓞 F) F g) * B g)
    (hB : ∀ g h, B (g * archInclN ι F h) = B g) (g : GL ι (AdeleRing (𝓞 F) F)) :
    archConvN ι F Φ α g = convN ι F Ψ α (archComponentN ι (𝓞 F) F g) * B g := by
  simp only [archConvN, convN, hΦ, hB, archComponentN_mul_archInclN]
  rw [← integral_mul_const]
  congr 1
  funext h
  ring

end Convolution

section FiniteInclusion

variable (F : Type) [Field F] [NumberField F]


public theorem adeleArch_finMatrixInclN (M : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) (i j : ι) :
    AdelicLevel.adeleArch (𝓞 F) F (finMatrixInclN ι F M i j) = (1 : Matrix ι ι (InfiniteAdeleRing F)) i j :=
  rfl

omit [Fintype ι] in

public theorem adeleFin_finMatrixInclN (M : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) (i j : ι) :
    AdelicLevel.adeleFin (𝓞 F) F (finMatrixInclN ι F M i j) = M i j :=
  rfl

omit [Fintype ι] in

public theorem finMatrixInclN_one : finMatrixInclN ι F (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) = 1 := by
  ext i j
  refine Prod.ext ?_ ?_
  · change (1 : Matrix ι ι (InfiniteAdeleRing F)) i j =
      AdelicLevel.adeleArch (𝓞 F) F ((1 : Matrix ι ι (AdeleRing (𝓞 F) F)) i j)
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  · change (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) i j =
      AdelicLevel.adeleFin (𝓞 F) F ((1 : Matrix ι ι (AdeleRing (𝓞 F) F)) i j)
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]


public theorem finMatrixInclN_mul (M N : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) :
    finMatrixInclN ι F (M * N) = finMatrixInclN ι F M * finMatrixInclN ι F N := by
  ext i j
  refine Prod.ext ?_ ?_
  · change (1 : Matrix ι ι (InfiniteAdeleRing F)) i j =
      AdelicLevel.adeleArch (𝓞 F) F ((finMatrixInclN ι F M * finMatrixInclN ι F N) i j)
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, adeleArch_finMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  · change (M * N) i j = AdelicLevel.adeleFin (𝓞 F) F ((finMatrixInclN ι F M * finMatrixInclN ι F N) i j)
    simp only [Matrix.mul_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, adeleFin_finMatrixInclN, adeleFin_finMatrixInclN]


public theorem archComponentN_finInclN (u : GL ι (FiniteAdeleRing (𝓞 F) F)) :
    archComponentN ι (𝓞 F) F (finInclN ι F u) = 1 := by
  ext i j
  rfl


public theorem componentAtN_finInclN (v : HeightOneSpectrum (𝓞 F)) (u : GL ι (FiniteAdeleRing (𝓞 F) F)) :
    componentAtN ι (𝓞 F) F v (finInclN ι F u) =
      Matrix.GeneralLinearGroup.map (AdelicLevel.finAdeleEval (𝓞 F) F v) u := by
  ext i j
  rfl


public theorem archMatrixInclN_mul_finMatrixInclN (M : Matrix ι ι (InfiniteAdeleRing F))
    (N : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) :
    archMatrixInclN ι F M * finMatrixInclN ι F N = finMatrixInclN ι F N * archMatrixInclN ι F M := by
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 F) F ((archMatrixInclN ι F M * finMatrixInclN ι F N) i j) =
      AdelicLevel.adeleArch (𝓞 F) F ((finMatrixInclN ι F N * archMatrixInclN ι F M) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, adeleArch_finMatrixInclN]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.mul_one, Matrix.one_mul]
  · change AdelicLevel.adeleFin (𝓞 F) F ((archMatrixInclN ι F M * finMatrixInclN ι F N) i j) =
      AdelicLevel.adeleFin (𝓞 F) F ((finMatrixInclN ι F N * archMatrixInclN ι F M) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN, adeleFin_finMatrixInclN]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul, Matrix.mul_one]


public theorem finInclN_mul_archInclN (u : GL ι (FiniteAdeleRing (𝓞 F) F)) (h : GL ι (InfiniteAdeleRing F)) :
    finInclN ι F u * archInclN ι F h = archInclN ι F h * finInclN ι F u :=
  Units.ext (archMatrixInclN_mul_finMatrixInclN ι F (h : Matrix ι ι (InfiniteAdeleRing F))
    (u : Matrix ι ι (FiniteAdeleRing (𝓞 F) F))).symm


public theorem archConvN_mul_finInclN (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (α : GL ι (InfiniteAdeleRing F) → ℂ)
    (u : GL ι (FiniteAdeleRing (𝓞 F) F)) (hΦ : ∀ g, Φ (g * finInclN ι F u) = Φ g) (g : GL ι (AdeleRing (𝓞 F) F)) :
    archConvN ι F Φ α (g * finInclN ι F u) = archConvN ι F Φ α g := by
  simp only [archConvN]
  congr 1
  funext h
  rw [mul_assoc, finInclN_mul_archInclN, ← mul_assoc, hΦ]

end FiniteInclusion

section FiniteAverage

variable (F : Type) [Field F] [NumberField F]
variable (U : Subgroup (GL ι (FiniteAdeleRing (𝓞 F) F))) [CompactSpace U]


public theorem borelSpace_compactBorelN : @BorelSpace U _ (compactBorelN ι F U) :=
  @BorelSpace.mk _ _ (compactBorelN ι F U) rfl


public theorem isProbabilityMeasure_compactHaarN : @IsProbabilityMeasure U (compactBorelN ι F U) (compactHaarN ι F U) := by
  letI := compactBorelN ι F U
  haveI := borelSpace_compactBorelN ι F U
  exact ⟨by rw [compactHaarN, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩


public theorem isMulLeftInvariant_compactHaarN :
    @Measure.IsMulLeftInvariant U (compactBorelN ι F U) _ (compactHaarN ι F U) := by
  letI := compactBorelN ι F U
  haveI := borelSpace_compactBorelN ι F U
  rw [compactHaarN]
  infer_instance


public theorem finAvgN_apply (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (g : GL ι (AdeleRing (𝓞 F) F)) :
    finAvgN ι F U Φ g =
      (letI := compactBorelN ι F U
       ∫ u : U, Φ (g * finInclN ι F (u : GL ι (FiniteAdeleRing (𝓞 F) F))) ∂(compactHaarN ι F U)) :=
  rfl


public theorem finAvgN_eq_self (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : ∀ g, ∀ u ∈ U, Φ (g * finInclN ι F u) = Φ g) (g : GL ι (AdeleRing (𝓞 F) F)) : finAvgN ι F U Φ g = Φ g := by
  simp only [finAvgN]
  letI := compactBorelN ι F U
  haveI := isProbabilityMeasure_compactHaarN ι F U
  simp only [hΦ g _ (SetLike.coe_mem _)]
  simp


public theorem finAvgN_comp_mul_left (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (a g : GL ι (AdeleRing (𝓞 F) F)) :
    finAvgN ι F U (fun x => Φ (a * x)) g = finAvgN ι F U Φ (a * g) := by
  simp only [finAvgN, mul_assoc]


public theorem finAvgN_mul_finInclN (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (g : GL ι (AdeleRing (𝓞 F) F))
    (u : GL ι (FiniteAdeleRing (𝓞 F) F)) (hu : u ∈ U) : finAvgN ι F U Φ (g * finInclN ι F u) = finAvgN ι F U Φ g := by
  simp only [finAvgN]
  letI := compactBorelN ι F U
  haveI := borelSpace_compactBorelN ι F U
  haveI := isMulLeftInvariant_compactHaarN ι F U
  rw [← integral_mul_left_eq_self (fun w : U => Φ (g * finInclN ι F (w : GL ι (FiniteAdeleRing (𝓞 F) F)))) ⟨u, hu⟩]
  simp only [Subgroup.coe_mul, map_mul, mul_assoc]

end FiniteAverage

end AutomorphicForm

end

end Vocabulary

section RealCore

open Matrix

noncomputable section

namespace AutomorphicForm.StandardKernel


public theorem entrySize_eq_sum (M : Matrix (Fin 3) (Fin 3) ℝ) : entrySize M = ∑ i, ∑ j, M i j ^ 2 := by
  simp only [entrySize, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm


public theorem entrySize_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ entrySize M := by
  rw [entrySize_eq_sum]
  positivity


public theorem entry_sq_le_entrySize (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : M i j ^ 2 ≤ entrySize M := by
  rw [entrySize_eq_sum]
  calc M i j ^ 2 ≤ ∑ j', M i j' ^ 2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)


public theorem entrySize_transpose (M : Matrix (Fin 3) (Fin 3) ℝ) : entrySize Mᵀ = entrySize M := by
  simp only [entrySize, Matrix.transpose_transpose]
  exact Matrix.trace_mul_comm M Mᵀ


public theorem entrySize_smul (c : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) : entrySize (c • M) = c ^ 2 * entrySize M := by
  simp only [entrySize, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, sq]


public theorem entrySize_one : entrySize 1 = 3 := by
  simp [entrySize]


public theorem entrySize_mul_of_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    entrySize (k * M) = entrySize M := by
  simp only [entrySize, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk, Matrix.one_mul]


public theorem adjugate_eq_det_smul_inv (X : Matrix (Fin 3) (Fin 3) ℝ) (hX : X.det ≠ 0) : adjugate X = X.det • X⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hX, one_smul]


public theorem adjugateT_one : adjugateT 1 = 1 := by
  simp [adjugateT]


public theorem transpose_inv_eq (M : Matrix (Fin 3) (Fin 3) ℝ) : (M⁻¹)ᵀ = (M.det)⁻¹ • adjugateT M := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.transpose_smul, adjugateT]


public theorem det_sq_of_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) : k.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hk
  rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at h


public theorem entrySize_adjugateT_mul_of_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1)
    (M : Matrix (Fin 3) (Fin 3) ℝ) : entrySize (adjugateT (k * M)) = entrySize (adjugateT M) := by
  have hdet : k.det ≠ 0 := fun h => by simpa [h] using det_sq_of_orth hk
  have hadj : adjugate k = k.det • kᵀ := by
    rw [adjugate_eq_det_smul_inv k hdet, Matrix.inv_eq_left_inv hk]
  rw [adjugateT, Matrix.adjugate_mul_distrib, hadj, Matrix.mul_smul, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, entrySize_smul, det_sq_of_orth hk, one_mul, entrySize_mul_of_orth hk, adjugateT]


public theorem adjugateT_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) :
    adjugateT ((M⁻¹)ᵀ) = (M.det)⁻¹ • M := by
  have hdet : ((M⁻¹)ᵀ).det = (M.det)⁻¹ := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hinv : ((M⁻¹)ᵀ)⁻¹ = Mᵀ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)]
  rw [adjugateT, adjugate_eq_det_smul_inv _ (by rw [hdet]; exact inv_ne_zero hM), hdet, hinv, Matrix.transpose_smul,
    Matrix.transpose_transpose]


public theorem det_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) : ((M⁻¹)ᵀ).det = (M.det)⁻¹ := by
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]


public theorem detSq_one : detSq 1 = 1 := by
  simp [detSq]


public theorem detSq_mul_of_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    detSq (k * M) = detSq M := by
  rw [detSq, detSq, Matrix.det_mul, mul_pow, det_sq_of_orth hk, one_mul]


public theorem detSq_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) : detSq ((M⁻¹)ᵀ) = (detSq M)⁻¹ := by
  rw [detSq, detSq, det_transpose_inv, inv_pow]


public theorem detSq_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ detSq M :=
  sq_nonneg _


public theorem entrySize_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) :
    entrySize ((M⁻¹)ᵀ) = (detSq M)⁻¹ * entrySize (adjugateT M) := by
  rw [transpose_inv_eq, entrySize_smul, detSq, inv_pow]


public theorem entrySize_adjugateT_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.det ≠ 0) :
    entrySize (adjugateT ((M⁻¹)ᵀ)) = (detSq M)⁻¹ * entrySize M := by
  rw [adjugateT_transpose_inv M hM, entrySize_smul, detSq, inv_pow]


public theorem reciprocalCutoff_eq_inv {t : ℝ} (h₁ : 1 / 2 ≤ t) (h₂ : t ≤ 4) : reciprocalCutoff t = t⁻¹ := by
  have hmem : t ∈ Metric.closedBall (9 / 4 : ℝ) unitCutoff.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(7 / 4 : ℝ) ≤ t - 9 / 4 ∧ t - 9 / 4 ≤ 7 / 4
    constructor <;> linarith
  rw [reciprocalCutoff, unitCutoff.one_of_mem_closedBall hmem, one_mul]


public theorem reciprocalCutoff_eq_zero {t : ℝ} (ht : |t| < 1 / 4) : reciprocalCutoff t = 0 := by
  have hdist : unitCutoff.rOut ≤ dist t (9 / 4 : ℝ) := by
    change (2 : ℝ) ≤ dist t (9 / 4)
    rw [Real.dist_eq]
    rcases abs_lt.mp ht with ⟨h₁, h₂⟩
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [reciprocalCutoff, unitCutoff.zero_of_le_dist hdist, zero_mul]


public theorem contDiff_reciprocalCutoff : ContDiff ℝ (⊤ : ℕ∞) reciprocalCutoff := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hball : Metric.ball (0 : ℝ) (1 / 4) ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hball] with s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    exact reciprocalCutoff_eq_zero hs
  · exact unitCutoff.contDiffAt.mul (contDiffAt_inv ℝ ht)


public theorem detCutoff_of_pos {t : ℝ} (ht : 0 < t) : detCutoff t = logBump (Real.log t) * logBump (-Real.log t) := by
  rw [detCutoff, if_neg (not_le.mpr ht)]


public theorem detCutoff_of_nonpos {t : ℝ} (ht : t ≤ 0) : detCutoff t = 0 := by
  rw [detCutoff, if_pos ht]


public theorem detCutoff_inv (t : ℝ) : detCutoff t⁻¹ = detCutoff t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [detCutoff_of_nonpos ht, detCutoff_of_nonpos (inv_nonpos.mpr ht)]
  · rw [detCutoff_of_pos ht, detCutoff_of_pos (inv_pos.mpr ht), Real.log_inv, neg_neg, mul_comm]


public theorem detCutoff_one : detCutoff 1 = 1 := by
  have h0 : logBump (0 : ℝ) = 1 :=
    logBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact logBump.rIn_pos.le)
  rw [detCutoff_of_pos one_pos, Real.log_one, neg_zero, h0, one_mul]


public theorem mem_of_detCutoff_ne_zero {t : ℝ} (h : detCutoff t ≠ 0) : 1 / 2 < t ∧ t < 2 := by
  have ht : 0 < t := by
    by_contra hle
    exact h (detCutoff_of_nonpos (not_lt.mp hle))
  rw [detCutoff_of_pos ht] at h
  have h₁ : logBump (Real.log t) ≠ 0 := left_ne_zero_of_mul h
  have hsupp : Real.log t ∈ Metric.ball (0 : ℝ) logBump.rOut := by
    rw [← logBump.support_eq]
    exact h₁
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hsupp
  change |Real.log t| < Real.log 2 at hsupp
  rcases abs_lt.mp hsupp with ⟨hlow, hhigh⟩
  constructor
  · have : Real.log (1 / 2) < Real.log t := by rw [one_div, Real.log_inv]; exact hlow
    exact (Real.log_lt_log_iff (by norm_num) ht).mp this
  · exact (Real.log_lt_log_iff ht (by norm_num)).mp hhigh


public theorem detCutoff_eq_zero_of_lt_half {t : ℝ} (ht : t < 1 / 2) : detCutoff t = 0 := by
  by_contra h
  exact absurd (mem_of_detCutoff_ne_zero h).1 (not_lt.mpr ht.le)


public theorem contDiff_detCutoff : ContDiff ℝ (⊤ : ℕ∞) detCutoff := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t (1 / 2) with ht | ht
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact detCutoff_eq_zero_of_lt_half hs
  · have hpos : 0 < t := by linarith
    have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => logBump (Real.log s) * logBump (-Real.log s)) t := by
      have hlog : ContDiffAt ℝ (⊤ : ℕ∞) Real.log t := Real.contDiffAt_log.mpr hpos.ne'
      exact (logBump.contDiffAt.comp t hlog).mul (logBump.contDiffAt.comp t hlog.neg)
    refine hsmooth.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hpos] with s hs
    exact detCutoff_of_pos hs


public theorem sizeBump_six : sizeBump (6 : ℝ) = 1 :=
  sizeBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact sizeBump.rIn_pos.le)


public theorem lt_eight_of_sizeBump_ne_zero {s : ℝ} (h : sizeBump s ≠ 0) : s < 8 := by
  have hs : s ∈ Metric.ball (6 : ℝ) sizeBump.rOut := by
    rw [← sizeBump.support_eq]
    exact h
  rw [Metric.mem_ball, Real.dist_eq] at hs
  change |s - 6| < 2 at hs
  linarith [(abs_lt.mp hs).2]


public theorem sizeInvariant_one : sizeInvariant 1 = 6 := by
  rw [sizeInvariant, entrySize_one, adjugateT_one, entrySize_one, detSq_one,
    reciprocalCutoff_eq_inv (by norm_num) (by norm_num)]
  norm_num


public theorem standardKernelCore_one : standardKernelCore 1 = 1 := by
  rw [standardKernelCore, sizeInvariant_one, detSq_one, sizeBump_six, detCutoff_one, one_mul]


public theorem standardKernelCore_mul_of_orth {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1)
    (M : Matrix (Fin 3) (Fin 3) ℝ) : standardKernelCore (k * M) = standardKernelCore M := by
  simp only [standardKernelCore, sizeInvariant, entrySize_mul_of_orth hk, entrySize_adjugateT_mul_of_orth hk,
    detSq_mul_of_orth hk]


public theorem standardKernelCore_transpose_inv (M : Matrix (Fin 3) (Fin 3) ℝ) :
    standardKernelCore ((M⁻¹)ᵀ) = standardKernelCore M := by
  by_cases hM : M.det = 0
  · have hinv : M⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit M (by rw [hM]; exact not_isUnit_zero)
    have h0 : detCutoff (detSq (0 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
      refine detCutoff_of_nonpos ?_
      rw [detSq, Matrix.det_zero, zero_pow two_ne_zero]
    rw [standardKernelCore, standardKernelCore, hinv, Matrix.transpose_zero, h0, mul_zero, detSq, hM,
      zero_pow two_ne_zero, detCutoff_of_nonpos le_rfl, mul_zero]
  · rw [standardKernelCore, standardKernelCore, detSq_transpose_inv, detCutoff_inv]
    by_cases hcut : detCutoff (detSq M) = 0
    · rw [hcut, mul_zero, mul_zero]
    · congr 2
      obtain ⟨hlow, hhigh⟩ := mem_of_detCutoff_ne_zero hcut
      have hQ : 0 < detSq M := by linarith
      have hQinv_low : 1 / 2 ≤ (detSq M)⁻¹ := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        nlinarith [mul_inv_cancel₀ hQ.ne', inv_pos.mpr hQ, hhigh]
      have hQinv_high : (detSq M)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ hQ (by norm_num)]
        linarith
      rw [sizeInvariant, sizeInvariant, entrySize_transpose_inv, entrySize_adjugateT_transpose_inv M hM,
        detSq_transpose_inv, reciprocalCutoff_eq_inv hQinv_low hQinv_high,
        reciprocalCutoff_eq_inv hlow.le (by linarith), inv_inv]
      field_simp
      ring


public theorem bound_of_standardKernelCore_ne_zero {M : Matrix (Fin 3) (Fin 3) ℝ} (h : standardKernelCore M ≠ 0) :
    M.det ≠ 0 ∧ entrySize M ≤ 8 ∧ entrySize M⁻¹ ≤ 8 := by
  have hbump : sizeBump (sizeInvariant M) ≠ 0 := left_ne_zero_of_mul h
  have hcut : detCutoff (detSq M) ≠ 0 := right_ne_zero_of_mul h
  obtain ⟨hlow, hhigh⟩ := mem_of_detCutoff_ne_zero hcut
  have hdet : M.det ≠ 0 := by
    intro h0
    rw [detSq, h0, zero_pow two_ne_zero] at hlow
    norm_num at hlow
  have hsize : sizeInvariant M < 8 := lt_eight_of_sizeBump_ne_zero hbump
  have hinv : entrySize M⁻¹ = entrySize (adjugateT M) * reciprocalCutoff (detSq M) := by
    rw [← entrySize_transpose (M⁻¹), entrySize_transpose_inv, reciprocalCutoff_eq_inv hlow.le (by linarith), mul_comm]
  have h₁ := entrySize_nonneg M
  have h₂ : 0 ≤ entrySize M⁻¹ := entrySize_nonneg _
  rw [sizeInvariant, ← hinv] at hsize
  exact ⟨hdet, by linarith, by linarith⟩


public theorem coreOfEntries_apply (M : Matrix (Fin 3) (Fin 3) ℝ) : coreOfEntries (fun i j => M i j) = standardKernelCore M :=
  rfl


public theorem contDiff_entrySize_of : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 3 → Fin 3 → ℝ => entrySize (Matrix.of m) := by
  simp only [entrySize_eq_sum, Matrix.of_apply]
  fun_prop


public theorem contDiff_detSq_of : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 3 → Fin 3 → ℝ => detSq (Matrix.of m) := by
  simp only [detSq, Matrix.det_fin_three, Matrix.of_apply]
  fun_prop


public theorem contDiff_entrySize_adjugateT_of :
    ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 3 → Fin 3 → ℝ => entrySize (adjugateT (Matrix.of m)) := by
  simp only [entrySize_eq_sum, adjugateT, Matrix.adjugate_fin_three, Matrix.transpose_apply, Matrix.of_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  fun_prop


public theorem contDiff_coreOfEntries : ContDiff ℝ (⊤ : ℕ∞) coreOfEntries := by
  have h₁ := contDiff_entrySize_of
  have h₂ := contDiff_detSq_of
  have h₃ := contDiff_entrySize_adjugateT_of
  have h₄ := contDiff_reciprocalCutoff
  have h₅ := contDiff_detCutoff
  have h₆ : ContDiff ℝ (⊤ : ℕ∞) (sizeBump : ℝ → ℝ) := sizeBump.contDiff
  have hinv : ContDiff ℝ (⊤ : ℕ∞) fun m : Fin 3 → Fin 3 → ℝ => sizeInvariant (Matrix.of m) := by
    simp only [sizeInvariant]
    exact h₁.add (h₃.mul (h₄.comp h₂))
  unfold coreOfEntries standardKernelCore
  exact (h₆.comp hinv).mul (h₅.comp h₂)

end AutomorphicForm.StandardKernel

end

end RealCore

section Kernel

open NumberField Matrix Topology
open scoped Classical

noncomputable section

namespace AutomorphicForm.StandardKernel


public theorem realCoord_apply (x : InfiniteAdeleRing ℚ) :
    realCoord x = InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x Rat.infinitePlace) :=
  rfl


public theorem continuous_ofReal : Continuous ofReal :=
  continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous


public theorem ofReal_realCoord (x : InfiniteAdeleRing ℚ) : ofReal (realCoord x) = x := by
  funext v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply _


public theorem realMat_eq (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    realMat g = (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).map realCoord :=
  rfl


public theorem realMat_mul (g h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : realMat (g * h) = realMat g * realMat h := by
  rw [realMat, realMat, realMat, map_mul, Units.val_mul]


public theorem realMat_inv (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : realMat g⁻¹ = (realMat g)⁻¹ := by
  rw [realMat, realMat, map_inv, Matrix.coe_units_inv]


public theorem realMat_one : realMat 1 = 1 := by
  rw [realMat, map_one, Units.val_one]


public theorem realMat_transposeInvN (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    realMat (transposeInvN (Fin 3) g) = ((realMat g)⁻¹)ᵀ := by
  rw [realMat_eq, coe_transposeInvN, Matrix.transpose_map, ← realMat_eq, realMat_inv]


public theorem realMat_orth {k : GL (Fin 3) (InfiniteAdeleRing ℚ)} (hk : k ∈ orthN (Fin 3) ℚ) :
    (realMat k)ᵀ * realMat k = 1 := by
  have h : (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ * k = 1 := hk
  have h' := congrArg (fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => M.map realCoord) h
  rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one realCoord (map_zero _) (map_one _)] at h'
  rw [realMat_eq]
  exact h'


public theorem standardKernel_one : standardKernel 1 = 1 := by
  rw [standardKernel, realMat_one, standardKernelCore_one, Complex.ofReal_one]


public theorem standardKernel_ne_zero : standardKernel ≠ 0 := fun h => by
  have := congrFun h 1
  rw [standardKernel_one, Pi.zero_apply] at this
  exact one_ne_zero this


public theorem standardKernel_transposeInvN (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    standardKernel (transposeInvN (Fin 3) g) = standardKernel g := by
  rw [standardKernel, standardKernel, realMat_transposeInvN, standardKernelCore_transpose_inv]


public theorem standardKernel_comp_transposeInvN : standardKernel ∘ transposeInvN (Fin 3) = standardKernel :=
  funext standardKernel_transposeInvN


public theorem standardKernel_mul_of_mem_orthN {k : GL (Fin 3) (InfiniteAdeleRing ℚ)} (hk : k ∈ orthN (Fin 3) ℚ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : standardKernel (k * g) = standardKernel g := by
  rw [standardKernel, standardKernel, realMat_mul, standardKernelCore_mul_of_orth (realMat_orth hk)]


public theorem isLeftOrthFiniteN_standardKernel : IsLeftOrthFiniteN (Fin 3) ℚ standardKernel := by
  refine ⟨{standardKernel}, fun k hk => ?_⟩
  have h : (fun x => standardKernel (k * x)) = standardKernel := funext fun x => standardKernel_mul_of_mem_orthN hk x
  rw [h]
  exact Submodule.subset_span (by simp)


public theorem mixedCoord_ringEquiv (x : InfiniteAdeleRing ℚ) :
    mixedCoord (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x) = realCoord x :=
  rfl


public theorem contDiff_mixedCoord : ContDiff ℝ (⊤ : ℕ∞) mixedCoord := by
  unfold mixedCoord
  fun_prop


public theorem contDiff_entryFunction : ContDiff ℝ (⊤ : ℕ∞) entryFunction := by
  have h₁ := contDiff_coreOfEntries
  have h₂ := contDiff_mixedCoord
  have h₃ : ContDiff ℝ (⊤ : ℕ∞)
      fun m : Fin 3 → Fin 3 → mixedEmbedding.mixedSpace ℚ => fun i j => mixedCoord (m i j) := by
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp (h₁.comp h₃)


public theorem standardKernel_eq_entryFunction (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    standardKernel g = entryFunction (archEntriesN (Fin 3) ℚ g) :=
  rfl


public theorem isCompact_entryBox : IsCompact entryBox :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc


public theorem mem_entryBox_of_entrySize_le {M : Matrix (Fin 3) (Fin 3) ℝ} (h : entrySize M ≤ 8) : M ∈ entryBox := by
  unfold entryBox
  intro i _ j _
  have h₁ := (entry_sq_le_entrySize M i j).trans h
  exact ⟨by nlinarith, by nlinarith⟩


public theorem isCompact_adelicEntryBox : IsCompact adelicEntryBox :=
  isCompact_entryBox.image (continuous_id.matrix_map continuous_ofReal)


public theorem mem_adelicEntryBox_of_entrySize_le {X : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)}
    (h : entrySize (X.map realCoord) ≤ 8) : X ∈ adelicEntryBox := by
  refine ⟨X.map realCoord, mem_entryBox_of_entrySize_le h, ?_⟩
  ext i j
  simp only [Matrix.map_apply, ofReal_realCoord]


public theorem isCompact_carrierSet : IsCompact carrierSet := by
  haveI : T2Space (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space (Fin 3 → Fin 3 → InfiniteAdeleRing ℚ))
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (isCompact_adelicEntryBox.prod (isCompact_adelicEntryBox.image MulOpposite.continuous_op))


public theorem isClosed_carrierSet : IsClosed carrierSet := by
  haveI : T2Space (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space (Fin 3 → Fin 3 → InfiniteAdeleRing ℚ))
  have hC := isCompact_adelicEntryBox.isClosed
  have hC' := (isCompact_adelicEntryBox.image MulOpposite.continuous_op).isClosed
  exact (hC.prod hC').preimage Units.continuous_embedProduct


public theorem mem_carrierSet_of_standardKernel_ne_zero {g : GL (Fin 3) (InfiniteAdeleRing ℚ)} (h : standardKernel g ≠ 0) :
    g ∈ carrierSet := by
  have hcore : standardKernelCore (realMat g) ≠ 0 := fun h0 => h (by rw [standardKernel, h0, Complex.ofReal_zero])
  obtain ⟨-, hg, hginv⟩ := bound_of_standardKernelCore_ne_zero hcore
  rw [← realMat_inv] at hginv
  have h₁ : (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) ∈ adelicEntryBox :=
    mem_adelicEntryBox_of_entrySize_le (by rw [← realMat_eq]; exact hg)
  have h₂ :
      ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) ∈ adelicEntryBox :=
    mem_adelicEntryBox_of_entrySize_le (by rw [← realMat_eq]; exact hginv)
  exact ⟨h₁, (g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)), h₂, rfl⟩


public theorem hasCompactSupport_standardKernel : HasCompactSupport standardKernel :=
  HasCompactSupport.intro' isCompact_carrierSet isClosed_carrierSet fun g hg => by
    by_contra h
    exact hg (mem_carrierSet_of_standardKernel_ne_zero h)


public theorem isArchTestFactorN_standardKernel : IsArchTestFactorN (Fin 3) ℚ standardKernel :=
  ⟨⟨entryFunction, contDiff_entryFunction, standardKernel_eq_entryFunction⟩, hasCompactSupport_standardKernel⟩


public theorem isSmoothingKernelN_standardKernel : IsSmoothingKernelN (Fin 3) ℚ standardKernel :=
  ⟨isArchTestFactorN_standardKernel, isLeftOrthFiniteN_standardKernel⟩


public theorem exists_isSmoothingKernelN_transposeInvN_one :
    ∃ α : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ,
      IsSmoothingKernelN (Fin 3) ℚ α ∧ α ∘ transposeInvN (Fin 3) = α ∧ α 1 = 1 :=
  ⟨standardKernel, isSmoothingKernelN_standardKernel, standardKernel_comp_transposeInvN, standardKernel_one⟩

end AutomorphicForm.StandardKernel

end

end Kernel

#check @AutomorphicForm.transposeInvN
#check @AutomorphicForm.archEntriesN
#check @AutomorphicForm.orthN
#check @AutomorphicForm.IsLeftOrthFiniteN
#check @AutomorphicForm.IsArchTestFactorN
#check @AutomorphicForm.IsSmoothingKernelN
#check @AutomorphicForm.archInclN
#check @AutomorphicForm.archGLHaarN
#check @AutomorphicForm.convN
#check @AutomorphicForm.archConvN
#check @AutomorphicForm.finInclN
#check @AutomorphicForm.compactHaarN
#check @AutomorphicForm.finAvgN
#print axioms AutomorphicForm.transposeInvN_mul
#print axioms AutomorphicForm.componentAtN_mul_archInclN
#print axioms AutomorphicForm.isHaarMeasure_archGLHaarN
#print axioms AutomorphicForm.archConvN_comp_mul_left
#print axioms AutomorphicForm.convN_mul_right
#print axioms AutomorphicForm.archConvN_eq_convN_mul
#print axioms AutomorphicForm.finInclN_mul_archInclN
#print axioms AutomorphicForm.archConvN_mul_finInclN
#print axioms AutomorphicForm.isProbabilityMeasure_compactHaarN
#print axioms AutomorphicForm.finAvgN_eq_self
#print axioms AutomorphicForm.finAvgN_mul_finInclN
#check @AutomorphicForm.StandardKernel.standardKernelCore
#print axioms AutomorphicForm.StandardKernel.standardKernelCore_one
#print axioms AutomorphicForm.StandardKernel.standardKernelCore_mul_of_orth
#print axioms AutomorphicForm.StandardKernel.standardKernelCore_transpose_inv
#print axioms AutomorphicForm.StandardKernel.bound_of_standardKernelCore_ne_zero
#print axioms AutomorphicForm.StandardKernel.contDiff_coreOfEntries
#check @AutomorphicForm.StandardKernel.standardKernel
#print axioms AutomorphicForm.StandardKernel.standardKernel_one
#print axioms AutomorphicForm.StandardKernel.standardKernel_comp_transposeInvN
#print axioms AutomorphicForm.StandardKernel.isSmoothingKernelN_standardKernel
#print axioms AutomorphicForm.StandardKernel.exists_isSmoothingKernelN_transposeInvN_one
