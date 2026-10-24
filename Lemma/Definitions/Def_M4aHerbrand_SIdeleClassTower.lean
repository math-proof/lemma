import Mathlib
import Lemma.Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Lemma.Definitions.Def_M4aHerbrand_AdeleBaseChange

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace M4aHerbrand

section RepRes

universe u

variable {G G' : Type u} [Group G] [Group G'] {M N : Type u} [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G' N]

def repHomResOfMulEquivariant (π : G' →* G) (f : M →* N) (hf : ∀ (g' : G') (m : M), f (π g' • m) = g' • f m) :
    Rep.res π (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction G' N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun g' => LinearMap.ext fun (x : Additive M) => by
    change Additive.ofMul (f (π g' • Additive.toMul x)) = Additive.ofMul (g' • f (Additive.toMul x))
    rw [hf]⟩

@[simp] lemma repHomResOfMulEquivariant_hom_apply (π : G' →* G) (f : M →* N)
    (hf : ∀ (g' : G') (m : M), f (π g' • m) = g' • f m) (x : Additive M) :
    (repHomResOfMulEquivariant π f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

end RepRes

namespace AdeleBaseChange

section Maps

variable {R F R' F' : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']

abbrev idelesMap (B : AdeleBaseChange R F R' F') : (AdeleRing R F)ˣ →* (AdeleRing R' F')ˣ := Units.map B.β.toMonoidHom

@[simp] lemma coe_idelesMap_apply (B : AdeleBaseChange R F R' F') (x : (AdeleRing R F)ˣ) :
    (B.idelesMap x : AdeleRing R' F') = B.β x := rfl

lemma map_principalIdeles_le (B : AdeleBaseChange R F R' F') :
    (principalIdeles R F).map B.idelesMap ≤ principalIdeles R' F' := by
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨Units.map (algebraMap F F').toMonoidHom u, Units.ext (B.β_compat (u : F)).symm⟩

def classMap (B : AdeleBaseChange R F R' F') : IdeleClassGroup R F →* IdeleClassGroup R' F' :=
  QuotientGroup.map _ _ B.idelesMap (Subgroup.map_le_iff_le_comap.1 B.map_principalIdeles_le)

@[simp] lemma classMap_mk (B : AdeleBaseChange R F R' F') (x : (AdeleRing R F)ˣ) :
    B.classMap (QuotientGroup.mk x) = QuotientGroup.mk (B.idelesMap x) := rfl

def MapsUnitIdeles (B : AdeleBaseChange R F R' F') (T : Set (HeightOneSpectrum R)) (T' : Set (HeightOneSpectrum R')) : Prop :=
  ∀ x : (AdeleRing R F)ˣ, x ∈ unitIdelesTrivialOn R F T → B.idelesMap x ∈ unitIdelesTrivialOn R' F' T'

variable {T : Set (HeightOneSpectrum R)} {T' : Set (HeightOneSpectrum R')}

lemma sClassKernel_le_comap (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T') :
    sClassKernel R F T ≤ (sClassKernel R' F' T').comap B.idelesMap :=
  sup_le (fun x hx => principalIdeles_le_sClassKernel R' F' T' (B.map_principalIdeles_le ⟨x, hx, rfl⟩))
    (fun x hx => unitIdelesTrivialOn_le_sClassKernel R' F' T' (hB x hx))

def sClassMap (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T') :
    SIdeleClassGroup R F T →* SIdeleClassGroup R' F' T' :=
  QuotientGroup.map _ _ B.idelesMap (B.sClassKernel_le_comap hB)

@[simp] lemma sClassMap_mk (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T') (x : (AdeleRing R F)ˣ) :
    B.sClassMap hB (QuotientGroup.mk x) = QuotientGroup.mk (B.idelesMap x) := rfl

lemma sClassMap_toSIdeleClass (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T') (c : IdeleClassGroup R F) :
    B.sClassMap hB (toSIdeleClass R F T c) = toSIdeleClass R' F' T' (B.classMap c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; rfl

lemma sClassMap_comp_toSIdeleClass (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T') :
    (B.sClassMap hB).comp (toSIdeleClass R F T) = (toSIdeleClass R' F' T').comp B.classMap :=
  MonoidHom.ext (B.sClassMap_toSIdeleClass hB)

def NormMapsPrincipal (B : AdeleBaseChange R F R' F') : Prop :=
  ∀ x : (AdeleRing R' F')ˣ, x ∈ principalIdeles R' F' → B.idelicNorm x ∈ principalIdeles R F

def NormMapsSClassKernel (B : AdeleBaseChange R F R' F') (T' : Set (HeightOneSpectrum R')) (T : Set (HeightOneSpectrum R)) :
    Prop :=
  ∀ x : (AdeleRing R' F')ˣ, x ∈ sClassKernel R' F' T' → B.idelicNorm x ∈ sClassKernel R F T

def classNorm (B : AdeleBaseChange R F R' F') (hN : B.NormMapsPrincipal) : IdeleClassGroup R' F' →* IdeleClassGroup R F :=
  QuotientGroup.map _ _ B.idelicNorm hN

@[simp] lemma classNorm_mk (B : AdeleBaseChange R F R' F') (hN : B.NormMapsPrincipal) (x : (AdeleRing R' F')ˣ) :
    B.classNorm hN (QuotientGroup.mk x) = QuotientGroup.mk (B.idelicNorm x) := rfl

def sClassNorm (B : AdeleBaseChange R F R' F') (hN : B.NormMapsSClassKernel T' T) :
    SIdeleClassGroup R' F' T' →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ B.idelicNorm hN

@[simp] lemma sClassNorm_mk (B : AdeleBaseChange R F R' F') (hN : B.NormMapsSClassKernel T' T) (x : (AdeleRing R' F')ˣ) :
    B.sClassNorm hN (QuotientGroup.mk x) = QuotientGroup.mk (B.idelicNorm x) := rfl

end Maps

section Tower

variable {R F R' F' R'' F'' : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
  [CommRing R''] [IsDedekindDomain R''] [Field F''] [Algebra R'' F''] [IsFractionRing R'' F'']
  [Algebra F F'] [Algebra F' F''] [Algebra F F'']
  {T : Set (HeightOneSpectrum R)} {T' : Set (HeightOneSpectrum R')} {T'' : Set (HeightOneSpectrum R'')}

lemma sClassMap_comp (B₁ : AdeleBaseChange R F R' F') (B₂ : AdeleBaseChange R' F' R'' F'') (B₃ : AdeleBaseChange R F R'' F'')
    (hcomp : ∀ x : AdeleRing R F, B₃.β x = B₂.β (B₁.β x))
    (h₁ : B₁.MapsUnitIdeles T T') (h₂ : B₂.MapsUnitIdeles T' T'') (h₃ : B₃.MapsUnitIdeles T T'') :
    B₃.sClassMap h₃ = (B₂.sClassMap h₂).comp (B₁.sClassMap h₁) :=
  MonoidHom.ext fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [MonoidHom.comp_apply, sClassMap_mk]
    exact congrArg QuotientGroup.mk (Units.ext (hcomp x))

lemma classMap_comp (B₁ : AdeleBaseChange R F R' F') (B₂ : AdeleBaseChange R' F' R'' F'') (B₃ : AdeleBaseChange R F R'' F'')
    (hcomp : ∀ x : AdeleRing R F, B₃.β x = B₂.β (B₁.β x)) :
    B₃.classMap = B₂.classMap.comp B₁.classMap :=
  MonoidHom.ext fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [MonoidHom.comp_apply, classMap_mk]
    exact congrArg QuotientGroup.mk (Units.ext (hcomp x))

lemma MapsUnitIdeles.comp {B₁ : AdeleBaseChange R F R' F'} {B₂ : AdeleBaseChange R' F' R'' F''} {B₃ : AdeleBaseChange R F R'' F''}
    (hcomp : ∀ x : AdeleRing R F, B₃.β x = B₂.β (B₁.β x))
    (h₁ : B₁.MapsUnitIdeles T T') (h₂ : B₂.MapsUnitIdeles T' T'') : B₃.MapsUnitIdeles T T'' := fun x hx => by
  have : B₃.idelesMap x = B₂.idelesMap (B₁.idelesMap x) := Units.ext (hcomp x)
  rw [this]; exact h₂ _ (h₁ x hx)

end Tower

section Equivariance

variable {R F R' F' : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']
  {L : Type} [Field L] [Algebra L F] [Algebra L F']
  {T : Set (HeightOneSpectrum R)} {T' : Set (HeightOneSpectrum R')}

def sClassMapRepHom (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T')
    (π : (F' ≃ₐ[L] F') →* (F ≃ₐ[L] F))
    [MulDistribMulAction (F ≃ₐ[L] F) (SIdeleClassGroup R F T)] [MulDistribMulAction (F' ≃ₐ[L] F') (SIdeleClassGroup R' F' T')]
    (h : ∀ (g' : F' ≃ₐ[L] F') (c : SIdeleClassGroup R F T), B.sClassMap hB (π g' • c) = g' • B.sClassMap hB c) :
    Rep.res π (Rep.ofMulDistribMulAction (F ≃ₐ[L] F) (SIdeleClassGroup R F T)) ⟶
      Rep.ofMulDistribMulAction (F' ≃ₐ[L] F') (SIdeleClassGroup R' F' T') :=
  repHomResOfMulEquivariant π (B.sClassMap hB) h

def classMapRepHom (B : AdeleBaseChange R F R' F') (π : (F' ≃ₐ[L] F') →* (F ≃ₐ[L] F))
    [MulDistribMulAction (F ≃ₐ[L] F) (IdeleClassGroup R F)] [MulDistribMulAction (F' ≃ₐ[L] F') (IdeleClassGroup R' F')]
    (h : ∀ (g' : F' ≃ₐ[L] F') (c : IdeleClassGroup R F), B.classMap (π g' • c) = g' • B.classMap c) :
    Rep.res π (Rep.ofMulDistribMulAction (F ≃ₐ[L] F) (IdeleClassGroup R F)) ⟶
      Rep.ofMulDistribMulAction (F' ≃ₐ[L] F') (IdeleClassGroup R' F') :=
  repHomResOfMulEquivariant π B.classMap h

lemma sClassMap_smul_of_descent (B : AdeleBaseChange R F R' F') (hB : B.MapsUnitIdeles T T')
    (π : (F' ≃ₐ[L] F') →* (F ≃ₐ[L] F)) (D : IdeleGaloisDescent R L F) (D' : IdeleGaloisDescent R' L F')
    (hβ : ∀ (g' : F' ≃ₐ[L] F') (x : AdeleRing R F), B.β (D.act (π g') x) = D'.act g' (B.β x))
    [MulDistribMulAction (F ≃ₐ[L] F) (SIdeleClassGroup R F T)] [MulDistribMulAction (F' ≃ₐ[L] F') (SIdeleClassGroup R' F' T')]
    (hactS : ∀ (g : F ≃ₐ[L] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T c = toSIdeleClass R F T (D.classAct g c))
    (hactS' : ∀ (g' : F' ≃ₐ[L] F') (c : IdeleClassGroup R' F'),
      g' • toSIdeleClass R' F' T' c = toSIdeleClass R' F' T' (D'.classAct g' c))
    (g' : F' ≃ₐ[L] F') (c : SIdeleClassGroup R F T) :
    B.sClassMap hB (π g' • c) = g' • B.sClassMap hB c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have lhs : π g' • (QuotientGroup.mk x : SIdeleClassGroup R F T) = QuotientGroup.mk (D.unitsAct (π g') x) := by
    simpa only [toSIdeleClass_mk, IdeleGaloisDescent.classAct_mk] using hactS (π g') (QuotientGroup.mk x)
  have rhs : g' • (QuotientGroup.mk (B.idelesMap x) : SIdeleClassGroup R' F' T') =
      QuotientGroup.mk (D'.unitsAct g' (B.idelesMap x)) := by
    simpa only [toSIdeleClass_mk, IdeleGaloisDescent.classAct_mk] using hactS' g' (QuotientGroup.mk (B.idelesMap x))
  rw [lhs, sClassMap_mk, sClassMap_mk, rhs]
  exact congrArg QuotientGroup.mk (Units.ext (hβ g' x))

lemma classMap_smul_of_descent (B : AdeleBaseChange R F R' F')
    (π : (F' ≃ₐ[L] F') →* (F ≃ₐ[L] F)) (D : IdeleGaloisDescent R L F) (D' : IdeleGaloisDescent R' L F')
    (hβ : ∀ (g' : F' ≃ₐ[L] F') (x : AdeleRing R F), B.β (D.act (π g') x) = D'.act g' (B.β x))
    [MulDistribMulAction (F ≃ₐ[L] F) (IdeleClassGroup R F)] [MulDistribMulAction (F' ≃ₐ[L] F') (IdeleClassGroup R' F')]
    (hact : ∀ (g : F ≃ₐ[L] F) (c : IdeleClassGroup R F), g • c = D.classAct g c)
    (hact' : ∀ (g' : F' ≃ₐ[L] F') (c : IdeleClassGroup R' F'), g' • c = D'.classAct g' c)
    (g' : F' ≃ₐ[L] F') (c : IdeleClassGroup R F) : B.classMap (π g' • c) = g' • B.classMap c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have lhs : π g' • (QuotientGroup.mk x : IdeleClassGroup R F) = QuotientGroup.mk (D.unitsAct (π g') x) := by
    rw [hact]; rfl
  have rhs : g' • (QuotientGroup.mk (B.idelesMap x) : IdeleClassGroup R' F') = QuotientGroup.mk (D'.unitsAct g' (B.idelesMap x)) := by
    rw [hact']; rfl
  rw [lhs, classMap_mk, classMap_mk, rhs]
  exact congrArg QuotientGroup.mk (Units.ext (hβ g' x))

end Equivariance

end AdeleBaseChange

end M4aHerbrand

end
