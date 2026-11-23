module

public import Def.LanglandsTunnell_CubicInduction_Carrier
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

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

noncomputable def transposeInvN (g : GL ι R) : GL ι R where
  val := ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ
  inv := ((g : GL ι R) : Matrix ι ι R)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

end TransposeInverse

section Kernels

variable (F : Type) [Field F]

noncomputable def archEntriesN (g : GL ι (InfiniteAdeleRing F)) : ι → ι → mixedEmbedding.mixedSpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F ((g : Matrix ι ι (InfiniteAdeleRing F)) i j)

noncomputable def orthN : Set (GL ι (InfiniteAdeleRing F)) :=
  {k | (k : Matrix ι ι (InfiniteAdeleRing F))ᵀ * k = 1}

noncomputable def IsLeftOrthFiniteN (α : GL ι (InfiniteAdeleRing F) → ℂ) : Prop :=
  ∃ S : Finset (GL ι (InfiniteAdeleRing F) → ℂ),
    ∀ k ∈ orthN ι F, (fun x => α (k * x)) ∈ Submodule.span ℂ (S : Set (GL ι (InfiniteAdeleRing F) → ℂ))

variable [NumberField F]

noncomputable def IsArchTestFactorN (α : GL ι (InfiniteAdeleRing F) → ℂ) : Prop :=
  (∃ Φ : (ι → ι → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, α g = Φ (archEntriesN ι F g)) ∧
    HasCompactSupport α

noncomputable def IsSmoothingKernelN (α : GL ι (InfiniteAdeleRing F) → ℂ) : Prop :=
  IsArchTestFactorN ι F α ∧ IsLeftOrthFiniteN ι F α

end Kernels

section Inclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable def archMatrixInclN (M : Matrix ι ι (InfiniteAdeleRing F)) : Matrix ι ι (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    ((M i j, (1 : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) i j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

omit [Fintype ι] in
noncomputable def archMatrixInclHomN : Matrix ι ι (InfiniteAdeleRing F) →* Matrix ι ι (AdeleRing (𝓞 F) F) where
  toFun := archMatrixInclN ι F
  map_one' := archMatrixInclN_one ι F
  map_mul' := archMatrixInclN_mul ι F

noncomputable def archInclN : GL ι (InfiniteAdeleRing F) →* GL ι (AdeleRing (𝓞 F) F) :=
  Units.map (archMatrixInclHomN ι F)

end Inclusion

section Haar

variable (F : Type) [Field F] [NumberField F]

@[reducible] noncomputable def archGLBorelN : MeasurableSpace (GL ι (InfiniteAdeleRing F)) :=
  borel _

omit [NumberField F] in

noncomputable def archGLHaarN : @Measure (GL ι (InfiniteAdeleRing F)) (archGLBorelN ι F) := by
  letI := archGLBorelN ι F
  haveI := borelSpace_archGLBorelN ι F
  haveI : T2Space (Matrix ι ι (InfiniteAdeleRing F)) := inferInstanceAs (T2Space (ι → ι → InfiniteAdeleRing F))
  haveI := locallyCompactSpace_archGLN ι F
  exact Measure.haar

end Haar

section Convolution

variable (F : Type) [Field F] [NumberField F]

noncomputable def convN (Ψ α : GL ι (InfiniteAdeleRing F) → ℂ) : GL ι (InfiniteAdeleRing F) → ℂ :=
  fun x =>
    (letI := archGLBorelN ι F
     ∫ h, Ψ (x * h) * α h ∂(archGLHaarN ι F))

noncomputable def archConvN (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) (α : GL ι (InfiniteAdeleRing F) → ℂ) :
    GL ι (AdeleRing (𝓞 F) F) → ℂ :=
  fun g =>
    (letI := archGLBorelN ι F
     ∫ h, Φ (g * archInclN ι F h) * α h ∂(archGLHaarN ι F))

end Convolution

section FiniteInclusion

variable (F : Type) [Field F] [NumberField F]

noncomputable def finMatrixInclN (M : Matrix ι ι (FiniteAdeleRing (𝓞 F) F)) : Matrix ι ι (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (((1 : Matrix ι ι (InfiniteAdeleRing F)) i j, M i j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

omit [Fintype ι] in
noncomputable def finMatrixInclHomN : Matrix ι ι (FiniteAdeleRing (𝓞 F) F) →* Matrix ι ι (AdeleRing (𝓞 F) F) where
  toFun := finMatrixInclN ι F
  map_one' := finMatrixInclN_one ι F
  map_mul' := finMatrixInclN_mul ι F

noncomputable def finInclN : GL ι (FiniteAdeleRing (𝓞 F) F) →* GL ι (AdeleRing (𝓞 F) F) :=
  Units.map (finMatrixInclHomN ι F)

end FiniteInclusion

section FiniteAverage

variable (F : Type) [Field F] [NumberField F]
variable (U : Subgroup (GL ι (FiniteAdeleRing (𝓞 F) F))) [CompactSpace U]

@[reducible] noncomputable def compactBorelN : MeasurableSpace U :=
  borel U

omit [CompactSpace U] in

noncomputable def compactHaarN : @Measure U (compactBorelN ι F U) := by
  letI := compactBorelN ι F U
  haveI := borelSpace_compactBorelN ι F U
  exact Measure.haarMeasure ⊤

noncomputable def finAvgN (Φ : GL ι (AdeleRing (𝓞 F) F) → ℂ) : GL ι (AdeleRing (𝓞 F) F) → ℂ :=
  fun g =>
    (letI := compactBorelN ι F U
     ∫ u : U, Φ (g * finInclN ι F (u : GL ι (FiniteAdeleRing (𝓞 F) F))) ∂(compactHaarN ι F U))

end FiniteAverage

end AutomorphicForm

end

end Vocabulary

section RealCore

open Matrix

noncomputable section

namespace AutomorphicForm.StandardKernel

noncomputable def entrySize (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Matrix.trace (Mᵀ * M)

noncomputable def adjugateT (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (adjugate M)ᵀ

noncomputable def detSq (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  M.det ^ 2

noncomputable def unitCutoff : ContDiffBump (9 / 4 : ℝ) :=
  ⟨7 / 4, 2, by norm_num, by norm_num⟩

noncomputable def reciprocalCutoff (t : ℝ) : ℝ :=
  unitCutoff t * t⁻¹

noncomputable def logBump : ContDiffBump (0 : ℝ) :=
  ⟨Real.log 2 / 2, Real.log 2, by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity,
    by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith⟩

noncomputable def detCutoff (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else logBump (Real.log t) * logBump (-Real.log t)

noncomputable def sizeBump : ContDiffBump (6 : ℝ) :=
  ⟨1, 2, one_pos, by norm_num⟩

noncomputable def sizeInvariant (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  entrySize M + entrySize (adjugateT M) * reciprocalCutoff (detSq M)

noncomputable def standardKernelCore (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  sizeBump (sizeInvariant M) * detCutoff (detSq M)

noncomputable def coreOfEntries (m : Fin 3 → Fin 3 → ℝ) : ℝ :=
  standardKernelCore (Matrix.of m)

end AutomorphicForm.StandardKernel

end

end RealCore

section Kernel

open NumberField Matrix Topology
open scoped Classical

noncomputable section

namespace AutomorphicForm.StandardKernel

noncomputable def realCoord : InfiniteAdeleRing ℚ →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
    (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace)

noncomputable def ofReal (r : ℝ) : InfiniteAdeleRing ℚ :=
  fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm r

noncomputable def realGL : GL (Fin 3) (InfiniteAdeleRing ℚ) →* GL (Fin 3) ℝ :=
  Units.map (realCoord.mapMatrix (m := Fin 3)).toMonoidHom

noncomputable def realMat (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  (realGL g : Matrix (Fin 3) (Fin 3) ℝ)

noncomputable def standardKernel (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  (standardKernelCore (realMat g) : ℂ)

noncomputable def mixedCoord (x : mixedEmbedding.mixedSpace ℚ) : ℝ :=
  x.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

noncomputable def entryFunction (m : Fin 3 → Fin 3 → mixedEmbedding.mixedSpace ℚ) : ℂ :=
  (coreOfEntries (fun i j => mixedCoord (m i j)) : ℂ)

noncomputable def entryBox : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-3 : ℝ) 3

noncomputable def adelicEntryBox : Set (Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  (fun Y : Matrix (Fin 3) (Fin 3) ℝ => Y.map ofReal) '' entryBox

noncomputable def carrierSet : Set (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  Units.embedProduct _ ⁻¹' (adelicEntryBox ×ˢ (MulOpposite.op '' adelicEntryBox))

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
