module

public import Mathlib
public import Def.M4aHerbrand_IdeleClassVocab
public import Theorem.Set.FiniteUnitIdelesOutside

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory Set

noncomputable section

namespace M4aHerbrand


section Carrier

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def infPart : (AdeleRing R F)ˣ →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing R F)).toMonoidHom

def finPart (w : HeightOneSpectrum R) : (AdeleRing R F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map ((RestrictedProduct.evalMonoidHom (fun v : HeightOneSpectrum R => v.adicCompletion F) w).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing R F)).toMonoidHom)

variable (R F)

def idelesTrivialOn (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ where
  carrier := {x | infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1}
  one_mem' := ⟨map_one _, fun w _ => map_one _⟩
  mul_mem' {x y} hx hy := ⟨by rw [map_mul, hx.1, hy.1, one_mul], fun w hw => by rw [map_mul, hx.2 w hw, hy.2 w hw, one_mul]⟩
  inv_mem' {x} hx := ⟨by rw [map_inv, hx.1, inv_one], fun w hw => by rw [map_inv, hx.2 w hw, inv_one]⟩

variable {R F} in
def unitIdelesTrivialOn (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ :=
  NumberField.AdeleRing.unitIdelesOutside R F T ⊓ idelesTrivialOn R F T

variable {R F}

end Carrier

section SClass

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def sClassKernel (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ :=
  principalIdeles R F ⊔ unitIdelesTrivialOn R F T

def sUnitClasses (T : Set (HeightOneSpectrum R)) : Subgroup (IdeleClassGroup R F) :=
  (unitIdelesTrivialOn R F T).map (QuotientGroup.mk' (principalIdeles R F))

abbrev SIdeleClassGroup (T : Set (HeightOneSpectrum R)) : Type _ := (AdeleRing R F)ˣ ⧸ sClassKernel R F T

def toSIdeleClass (T : Set (HeightOneSpectrum R)) : IdeleClassGroup R F →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by simpa [Subgroup.comap_id] using principalIdeles_le_sClassKernel R F T)

namespace SIdeleClassGroup

variable {R F}

def ofLE {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') : SIdeleClassGroup R F T' →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by simpa using sClassKernel_antitone R F h)

end SIdeleClassGroup

end SClass

section Descent

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

namespace IdeleGaloisDescent

@[reducible] def classMulDistribMulAction (D : IdeleGaloisDescent R E F) :
    MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup R F) where
  smul g c := D.classAct g c
  one_smul c := D.classAct_one c
  mul_smul g h c := D.classAct_mul g h c
  smul_one g := map_one (D.classAct g)
  smul_mul g x y := map_mul (D.classAct g) x y

def StabilizesUnitIdeles (D : IdeleGaloisDescent R E F) (T : Set (HeightOneSpectrum R)) : Prop :=
  ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing R F)ˣ), x ∈ unitIdelesTrivialOn R F T → D.unitsAct g x ∈ unitIdelesTrivialOn R F T

variable {T : Set (HeightOneSpectrum R)}

def sClassAct (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F) :
    SIdeleClassGroup R F T →* SIdeleClassGroup R F T :=
  QuotientGroup.map _ _ (D.unitsAct g).toMonoidHom (D.sClassKernel_le_comap_unitsAct hD g)

@[reducible] def sClassMulDistribMulAction (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) :
    MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T) where
  smul g c := D.sClassAct hD g c
  one_smul c := D.sClassAct_one hD c
  mul_smul g h c := D.sClassAct_mul hD g h c
  smul_one g := map_one (D.sClassAct hD g)
  smul_mul g x y := map_mul (D.sClassAct hD g) x y

end IdeleGaloisDescent

end Descent

section RepHoms

universe u

variable {G : Type u} [Group G] {M N : Type u} [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]

def repHomOfMulEquivariant (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    Rep.ofMulDistribMulAction G M ⟶ Rep.ofMulDistribMulAction G N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun g => LinearMap.ext fun x => by
    change Additive.ofMul (f (g • Additive.toMul x)) = Additive.ofMul (g • f (Additive.toMul x))
    rw [hf]⟩

variable {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {Γ : Type} [Group Γ]

def toSIdeleClassRepHom (T : Set (HeightOneSpectrum R)) [MulDistribMulAction Γ (IdeleClassGroup R F)]
    [MulDistribMulAction Γ (SIdeleClassGroup R F T)]
    (h : ∀ (g : Γ) (c : IdeleClassGroup R F), toSIdeleClass R F T (g • c) = g • toSIdeleClass R F T c) :
    Rep.ofMulDistribMulAction Γ (IdeleClassGroup R F) ⟶ Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T) :=
  repHomOfMulEquivariant (toSIdeleClass R F T) h

def SIdeleClassGroup.ofLERepHom {T T' : Set (HeightOneSpectrum R)} (hTT' : T ⊆ T')
    [MulDistribMulAction Γ (SIdeleClassGroup R F T')] [MulDistribMulAction Γ (SIdeleClassGroup R F T)]
    (h : ∀ (g : Γ) (c : SIdeleClassGroup R F T'), SIdeleClassGroup.ofLE hTT' (g • c) = g • SIdeleClassGroup.ofLE hTT' c) :
    Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T') ⟶ Rep.ofMulDistribMulAction Γ (SIdeleClassGroup R F T) :=
  repHomOfMulEquivariant (SIdeleClassGroup.ofLE hTT') h

end RepHoms

end M4aHerbrand

namespace NumberField

variable (E F : Type*) [Field E] [Field F] [Algebra E F]

def placesOver (S : Set (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 F)) :=
  {w | ∃ v ∈ S, w.asIdeal.under (𝓞 E) = v.asIdeal}

variable {E} in
def placesOverPrimes (S : Set Nat.Primes) : Set (HeightOneSpectrum (𝓞 F)) :=
  {w | ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal}

end NumberField

end

end
