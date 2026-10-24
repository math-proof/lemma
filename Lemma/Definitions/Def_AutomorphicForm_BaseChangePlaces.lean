import Lemma.Definitions.Def_AutomorphicForm_TwistedOrbital
import Lemma.Definitions.Def_M4aHerbrand_GenuineDescent

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

section Projections

variable (K : Type) [Field K] [NumberField K]

def adeleArchAlgHom : AdeleRing (𝓞 K) K →ₐ[K] InfiniteAdeleRing K :=
  { AdelicLevel.adeleArch (𝓞 K) K with commutes' := fun _ => rfl }

def adelePlaceAlgHom (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K :=
  { (AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K) with
    commutes' := fun _ => rfl }

@[simp] theorem adeleArchAlgHom_apply (a : AdeleRing (𝓞 K) K) : adeleArchAlgHom K a = a.1 := rfl

@[simp] theorem adelePlaceAlgHom_apply (v : HeightOneSpectrum (𝓞 K)) (a : AdeleRing (𝓞 K) K) :
    adelePlaceAlgHom K v a = a.2 v := rfl

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

def tensorArchHom : L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] InfiniteAdeleRing K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (adeleArchAlgHom K)

def tensorPlaceHom (v : HeightOneSpectrum (𝓞 K)) :
    L ⊗[K] AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] v.adicCompletion K :=
  Algebra.TensorProduct.map (AlgHom.id K L) (adelePlaceAlgHom K v)

omit [NumberField L] in
@[simp] theorem tensorArchHom_tmul (l : L) (a : AdeleRing (𝓞 K) K) :
    tensorArchHom K L (l ⊗ₜ a) = l ⊗ₜ a.1 := rfl

omit [NumberField L] in
@[simp] theorem tensorPlaceHom_tmul (v : HeightOneSpectrum (𝓞 K)) (l : L) (a : AdeleRing (𝓞 K) K) :
    tensorPlaceHom K L v (l ⊗ₜ a) = l ⊗ₜ a.2 v := rfl

def tensorArch : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (tensorArchHom K L).toRingHom

def tensorPlace (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (tensorPlaceHom K L v).toRingHom

omit [NumberField L] in
theorem tensorArch_apply (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (i j : Fin 2) :
    (tensorArch K L x : Matrix (Fin 2) (Fin 2) _) i j = tensorArchHom K L ((x : Matrix (Fin 2) (Fin 2) _) i j) :=
  rfl

omit [NumberField L] in
theorem tensorPlace_apply (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (i j : Fin 2) :
    (tensorPlace K L v x : Matrix (Fin 2) (Fin 2) _) i j =
      tensorPlaceHom K L v ((x : Matrix (Fin 2) (Fin 2) _) i j) :=
  rfl

def baseChangeEquiv : L ⊗[K] AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 L) L :=
  (Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L)

def baseChangeGL : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* GL (Fin 2) (AdeleRing (𝓞 L) L) :=
  Matrix.GeneralLinearGroup.map (baseChangeEquiv K L).toRingHom

theorem baseChangeGL_eq :
    baseChangeGL K L = Matrix.GeneralLinearGroup.map
      (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
        (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) := rfl

theorem baseChangeEquiv_tmul_fst (l : L) (a : AdeleRing (𝓞 K) K) :
    (baseChangeEquiv K L (l ⊗ₜ a)).1 = archIdent K L (l ⊗ₜ a.1) := by
  obtain ⟨a₁, a₂⟩ := a
  rfl

theorem baseChangeEquiv_tmul_one (l : L) :
    baseChangeEquiv K L (l ⊗ₜ 1) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  M4aHerbrand.Bridge.genuineRingEquiv_one_tmul K L l

theorem baseChangeEquiv_one_tmul (a : AdeleRing (𝓞 K) K) :
    baseChangeEquiv K L (1 ⊗ₜ a) = M4aHerbrand.Bridge.genuineβ K L a :=
  M4aHerbrand.Bridge.genuineRingEquiv_tmul_one K L a

theorem fst_baseChangeEquiv (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    (baseChangeEquiv K L z).1 = archIdent K L (tensorArchHom K L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul l a => rw [baseChangeEquiv_tmul_fst, tensorArchHom_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]; rfl

theorem semiLocalEval_algebraMap (v : HeightOneSpectrum (𝓞 K)) (l : L) :
    semiLocalEval K L v (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) = l ⊗ₜ 1 := by
  show (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
      (fun w : v.Extension (𝓞 L) => (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) w.1) = l ⊗ₜ 1
  rw [AlgEquiv.symm_apply_eq]
  have h : (fun w : v.Extension (𝓞 L) => (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) w.1) =
      algebraMap L (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) l := by
    funext w; rfl
  rw [h, show l ⊗ₜ[K] (1 : v.adicCompletion K) = algebraMap L (L ⊗[K] v.adicCompletion K) l from rfl,
    AlgEquiv.commutes]

theorem semiLocalEval_finiteConorm (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 K) K) :
    semiLocalEval K L v (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) a) = 1 ⊗ₜ a v := by
  show (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
      (fun w : v.Extension (𝓞 L) => (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) a) w.1) = 1 ⊗ₜ a v
  rw [AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w, rfl⟩ := w
  rw [M4aHerbrand.Bridge.finiteConorm_apply]
  show _ = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) _ (1 ⊗ₜ[K] a _) ⟨w, rfl⟩
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]
  rfl

theorem semiLocalEval_snd_baseChangeEquiv (v : HeightOneSpectrum (𝓞 K)) (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    semiLocalEval K L v (baseChangeEquiv K L z).2 = tensorPlaceHom K L v z := by
  have hsnd : ∀ p q : AdeleRing (𝓞 L) L, (p * q).2 = p.2 * q.2 := fun _ _ => rfl
  have hadd : ∀ p q : AdeleRing (𝓞 L) L, (p + q).2 = p.2 + q.2 := fun _ _ => rfl
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, show (0 : AdeleRing (𝓞 L) L).2 = 0 from rfl, map_zero]
  | tmul l a =>
    have h : l ⊗ₜ[K] a = (l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K)) * ((1 : L) ⊗ₜ[K] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul (baseChangeEquiv K L), hsnd, map_mul (semiLocalEval K L v), map_mul (tensorPlaceHom K L v),
      baseChangeEquiv_tmul_one, baseChangeEquiv_one_tmul, M4aHerbrand.Bridge.genuineβ_snd]
    show semiLocalEval K L v (algebraMap L (FiniteAdeleRing (𝓞 L) L) l) *
        semiLocalEval K L v (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K L (𝓞 L) a.2) = _
    rw [semiLocalEval_algebraMap, semiLocalEval_finiteConorm, tensorPlaceHom_tmul, tensorPlaceHom_tmul,
      show (1 : AdeleRing (𝓞 K) K).2 v = 1 from rfl]
  | add x y hx hy =>
    rw [map_add (baseChangeEquiv K L), hadd, map_add (semiLocalEval K L v), map_add (tensorPlaceHom K L v),
      hx, hy]

theorem glArch_baseChangeGL (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    AdelicLevel.glArch (𝓞 L) L (baseChangeGL K L x) = archIdentGL K L (tensorArch K L x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact fst_baseChangeEquiv K L _

theorem semiLocalComponent_glFin_baseChangeGL (v : HeightOneSpectrum (𝓞 K))
    (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (baseChangeGL K L x)) = tensorPlace K L v x := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  exact semiLocalEval_snd_baseChangeEquiv K L v _

omit [NumberField L] in
theorem tensorArchHom_includeRight (a : AdeleRing (𝓞 K) K) :
    tensorArchHom K L ((1 : L) ⊗ₜ a) = (1 : L) ⊗ₜ a.1 := rfl

omit [NumberField L] in
theorem tensorArch_toTensorGL (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    tensorArch K L (toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K g) :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

omit [NumberField L] in
theorem tensorPlace_toTensorGL (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    tensorPlace K L v (toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      toTensorGL K L (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g)) :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

variable (σ : L ≃ₐ[K] L)

omit [NumberField L] in
theorem tensorArchHom_sigmaTensor (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    tensorArchHom K L (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (InfiniteAdeleRing K) σ (tensorArchHom K L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField L] in
theorem tensorPlaceHom_sigmaTensor (v : HeightOneSpectrum (𝓞 K)) (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    tensorPlaceHom K L v (sigmaTensor K L (AdeleRing (𝓞 K) K) σ z) =
      sigmaTensor K L (v.adicCompletion K) σ (tensorPlaceHom K L v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField L] in
theorem tensorArch_sigmaGL (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    tensorArch K L (sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
      sigmaGL K L (InfiniteAdeleRing K) σ (tensorArch K L x) :=
  Matrix.GeneralLinearGroup.ext fun _ _ => tensorArchHom_sigmaTensor K L σ _

omit [NumberField L] in
theorem tensorPlace_sigmaGL (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    tensorPlace K L v (sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
      sigmaGL K L (v.adicCompletion K) σ (tensorPlace K L v x) :=
  Matrix.GeneralLinearGroup.ext fun _ _ => tensorPlaceHom_sigmaTensor K L σ v _

end Projections

section Topology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in

theorem rightActions_smul_eq (A : Type*) [CommRing A] [Algebra K A] (a : A) (z : L ⊗[K] A) :
    a • z = ((1 : L) ⊗ₜ[K] a) * z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul l b =>
    rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, TensorProduct.comm_symm_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem isModuleTopology_adeleRing :
    letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
    IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  exact M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
    (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)

def baseChangeLinear :
    letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
    (L ⊗[K] AdeleRing (𝓞 K) K) →ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  { toFun := baseChangeEquiv K L
    map_add' := map_add _
    map_smul' := fun a z => by
      rw [rightActions_smul_eq, map_mul, baseChangeEquiv_one_tmul, RingHom.id_apply, Algebra.smul_def]
      rfl }

def baseChangeLinearSymm :
    letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
    AdeleRing (𝓞 L) L →ₗ[AdeleRing (𝓞 K) K] (L ⊗[K] AdeleRing (𝓞 K) K) :=
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  { toFun := (baseChangeEquiv K L).symm
    map_add' := map_add _
    map_smul' := fun a y => by
      apply (baseChangeEquiv K L).injective
      rw [RingEquiv.apply_symm_apply, RingHom.id_apply, rightActions_smul_eq, map_mul,
        baseChangeEquiv_one_tmul, RingEquiv.apply_symm_apply, Algebra.smul_def]
      rfl }

def baseChangeHomeomorph : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ AdeleRing (𝓞 L) L :=
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI := isModuleTopology_adeleRing K L
  haveI : ContinuousAdd (L ⊗[K] AdeleRing (𝓞 K) K) := (isTopologicalRing_tensor K L _).toContinuousAdd
  { toEquiv := (baseChangeEquiv K L).toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (baseChangeLinear K L)
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (baseChangeLinearSymm K L) }

theorem baseChangeHomeomorph_apply (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    baseChangeHomeomorph K L z = baseChangeEquiv K L z := rfl

theorem continuous_baseChangeEquiv : Continuous (baseChangeEquiv K L) :=
  (baseChangeHomeomorph K L).continuous

theorem continuous_baseChangeEquiv_symm : Continuous (baseChangeEquiv K L).symm :=
  (baseChangeHomeomorph K L).symm.continuous

def archIdentEquiv : (L ⊗[K] InfiniteAdeleRing K) ≃+* InfiniteAdeleRing L :=
  (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.trans
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv

theorem archIdentEquiv_apply (z : L ⊗[K] InfiniteAdeleRing K) : archIdentEquiv K L z = archIdent K L z := rfl

theorem archIdentEquiv_one_tmul (a : InfiniteAdeleRing K) :
    archIdentEquiv K L (1 ⊗ₜ a) =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm a := rfl

theorem isModuleTopology_infiniteAdeleRing :
    letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
    IsModuleTopology (InfiniteAdeleRing K) (InfiniteAdeleRing L) := by
  letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let te := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeAlgEquiv
  haveI : Module.Free (InfiniteAdeleRing K) (InfiniteAdeleRing L) := Module.Free.of_equiv te.toLinearEquiv
  haveI : Module.Finite (InfiniteAdeleRing K) (InfiniteAdeleRing L) := Module.Finite.equiv te.toLinearEquiv
  exact M4aHerbrand.Bridge.isModuleTopology_of_continuous_algebraMap_of_sigmaCompact
    M4aHerbrand.ArchSemilocal.continuous_conorm

def archIdentLinear :
    letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
    (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] InfiniteAdeleRing L :=
  letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
  { toFun := archIdentEquiv K L
    map_add' := map_add _
    map_smul' := fun a z => by
      rw [rightActions_smul_eq, map_mul, archIdentEquiv_one_tmul, RingHom.id_apply, Algebra.smul_def]
      rfl }

def archIdentLinearSymm :
    letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
    InfiniteAdeleRing L →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
  letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
  { toFun := (archIdentEquiv K L).symm
    map_add' := map_add _
    map_smul' := fun a y => by
      apply (archIdentEquiv K L).injective
      rw [RingEquiv.apply_symm_apply, RingHom.id_apply, rightActions_smul_eq, map_mul,
        archIdentEquiv_one_tmul, RingEquiv.apply_symm_apply, Algebra.smul_def]
      rfl }

def archIdentHomeomorph : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ InfiniteAdeleRing L :=
  letI := (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).adeleAlgebra
  haveI := isModuleTopology_infiniteAdeleRing K L
  haveI : ContinuousAdd (L ⊗[K] InfiniteAdeleRing K) := (isTopologicalRing_tensor K L _).toContinuousAdd
  { toEquiv := (archIdentEquiv K L).toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (archIdentLinear K L)
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (archIdentLinearSymm K L) }

theorem archIdentHomeomorph_apply (z : L ⊗[K] InfiniteAdeleRing K) :
    archIdentHomeomorph K L z = archIdent K L z := rfl

theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_matrix fun i j => hf.comp ((Units.continuous_val).matrix_elem i j)
  · have h : (fun g : GL (Fin 2) A => ((Matrix.GeneralLinearGroup.map (n := Fin 2) f g)⁻¹).val) =
        fun g => (Matrix.GeneralLinearGroup.map (n := Fin 2) f g⁻¹).val := by
      funext g; rw [map_inv]
    rw [h]
    exact continuous_matrix fun i j => hf.comp ((Units.continuous_val.comp continuous_inv).matrix_elem i j)

def glCongr {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) : GL (Fin 2) A ≃ₜ* GL (Fin 2) B :=
  { Units.mapEquiv (e.mapMatrix (m := Fin 2)).toMulEquiv with
    continuous_toFun := continuous_glMap e.toRingHom he
    continuous_invFun := continuous_glMap e.symm.toRingHom he' }

theorem glCongr_apply {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (g : GL (Fin 2) A) :
    glCongr e he he' g = Matrix.GeneralLinearGroup.map e.toRingHom g := rfl

def baseChangeGLEquiv : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ* GL (Fin 2) (AdeleRing (𝓞 L) L) :=
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  glCongr (baseChangeEquiv K L) (continuous_baseChangeEquiv K L) (continuous_baseChangeEquiv_symm K L)

def archIdentGLEquiv : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* GL (Fin 2) (InfiniteAdeleRing L) :=
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  glCongr (archIdentEquiv K L) (archIdentHomeomorph K L).continuous (archIdentHomeomorph K L).symm.continuous

theorem archIdentGLEquiv_apply (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    archIdentGLEquiv K L x = archIdentGL K L x := rfl

end Topology

section Consequences

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem baseChangeGLEquiv_apply (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    baseChangeGLEquiv K L x = baseChangeGL K L x := rfl

theorem semiLocalEval_eq (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a = (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
      (fun w : v.Extension (𝓞 L) => a w.1) := rfl

theorem semiLocalHomeomorph_eq (v : HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v x = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x := rfl

theorem continuous_semiLocalEval (v : HeightOneSpectrum (𝓞 K)) : Continuous (semiLocalEval K L v) := by
  have h : (semiLocalEval K L v : FiniteAdeleRing (𝓞 L) L → L ⊗[K] v.adicCompletion K) =
      (semiLocalHomeomorph K L v).symm ∘ fun a w => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
    funext a
    rw [Function.comp_apply, eq_comm, Homeomorph.symm_apply_eq, semiLocalHomeomorph_eq, semiLocalEval_eq,
      AlgEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact (semiLocalHomeomorph K L v).symm.continuous.comp
    (continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1)

theorem continuous_semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (semiLocalComponent K L v) :=
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  continuous_glMap _ (continuous_semiLocalEval K L v)

theorem continuous_tensorArch : Continuous (tensorArch K L) := by
  have h : (tensorArch K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
      (archIdentGLEquiv K L).symm ∘ AdelicLevel.glArch (𝓞 L) L ∘ baseChangeGLEquiv K L := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, eq_comm, ContinuousMulEquiv.symm_apply_eq,
      baseChangeGLEquiv_apply, glArch_baseChangeGL]
    rfl
  rw [h]
  exact (archIdentGLEquiv K L).symm.continuous.comp
    ((AdelicLevel.continuous_glArch (𝓞 L) L).comp (baseChangeGLEquiv K L).continuous)

theorem continuous_tensorPlace (v : HeightOneSpectrum (𝓞 K)) : Continuous (tensorPlace K L v) := by
  have h : (tensorPlace K L v : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      semiLocalComponent K L v ∘ AdelicLevel.glFin (𝓞 L) L ∘ baseChangeGLEquiv K L := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, baseChangeGLEquiv_apply, semiLocalComponent_glFin_baseChangeGL]
  rw [h]
  exact (continuous_semiLocalComponent K L v).comp
    ((AdelicLevel.continuous_glFin (𝓞 L) L).comp (baseChangeGLEquiv K L).continuous)

theorem matrix_eq_of_forall_semiLocalEval_mapMatrix_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      (semiLocalEval K L v).mapMatrix M = (semiLocalEval K L v).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h (HeightOneSpectrum.under (𝓞 K) w)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, semiLocalEval_eq] at hw
  exact congrArg _ (congrFun ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L)
    (HeightOneSpectrum.under (𝓞 K) w)).symm.injective hw) ⟨w, rfl⟩)

theorem eq_of_tensorArch_eq_of_forall_tensorPlace_eq {x y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)}
    (h₁ : tensorArch K L x = tensorArch K L y) (h₂ : ∀ v : HeightOneSpectrum (𝓞 K), tensorPlace K L v x = tensorPlace K L v y) :
    x = y := by
  apply (baseChangeGLEquiv K L).injective
  rw [baseChangeGLEquiv_apply, baseChangeGLEquiv_apply]
  have e₁ : (AdelicLevel.glArch (𝓞 L) L (baseChangeGL K L x)).val =
      (AdelicLevel.glArch (𝓞 L) L (baseChangeGL K L y)).val := by
    rw [glArch_baseChangeGL, glArch_baseChangeGL, h₁]
  have e₂ : (AdelicLevel.glFin (𝓞 L) L (baseChangeGL K L x)).val =
      (AdelicLevel.glFin (𝓞 L) L (baseChangeGL K L y)).val := by
    refine matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L fun v => ?_
    have hv : (semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (baseChangeGL K L x))).val =
        (semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (baseChangeGL K L y))).val := by
      rw [semiLocalComponent_glFin_baseChangeGL, semiLocalComponent_glFin_baseChangeGL, h₂ v]
    ext i j
    exact congrFun (congrFun hv i) j
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · exact congrFun (congrFun e₁ i) j
  · exact congrFun (congrFun e₂ i) j

end Consequences

end AutomorphicForm

end
