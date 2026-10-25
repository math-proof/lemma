import Instance.LanglandsTunnell_ArtinFrobenius
import Structure.M4aHerbrand_IdeleClassVocab
import Instance.LanglandsTunnell_ArtinCoreCTM

set_option autoImplicit false

noncomputable section

open Deep.NTSupply NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace HeckeCharacter

section RelNorm

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

def placeUnder' (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 k) :=
  ⟨w.asIdeal.under (𝓞 k), inferInstance,
    fun h => w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩

omit [NumberField k] [NumberField E] in
theorem placeUnder'_asIdeal (w : HeightOneSpectrum (𝓞 E)) :
    (placeUnder' k E w).asIdeal = w.asIdeal.under (𝓞 k) := rfl

abbrev modulusExt (𝔠 : Ideal (𝓞 k)) : Ideal (𝓞 E) := 𝔠.map (algebraMap (𝓞 k) (𝓞 E))

def fracRelNormUnit : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w =>
    primeUnit k (placeUnder' k E w) ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal))

theorem placeUnder'_dvd_iff (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    (placeUnder' k E w).asIdeal ∣ 𝔠 ↔ w.asIdeal ∣ modulusExt k E 𝔠 := by
  rw [placeUnder'_asIdeal, modulusExt, Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap]

def gcopNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : ↥(coprimeToModulus k 𝔠) := by
  classical
  exact if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
    then ⟨primeUnit k (placeUnder' k E w) ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal),
      pow_mem (primeUnit_mem_coprimeToModulus k h) _⟩
    else 1

theorem coe_raySymbol_gcop_eq_fracRelNormUnit' {𝔠 : Ideal (𝓞 k)}
    (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((raySymbol E (gcopNC2 k E 𝔠) (Y : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E Y := by
  unfold raySymbol
  refine (MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) _)).trans ?_
  rw [show fracRelNormUnit k E Y
      = ∏ᶠ w, (primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal))
          ^ FractionalIdeal.count E w (Y : FractionalIdeal ((𝓞 E)⁰) E) from rfl]
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  · have hct : FractionalIdeal.count E w (Y : FractionalIdeal ((𝓞 E)⁰) E) = 0 :=
      (mem_coprimeToModulus_iff E).mp hY w ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  · simp only [gcopNC2]; rw [dif_pos hw]

theorem fracRelNormUnit_mem_coprimeToModulus {𝔠 : Ideal (𝓞 k)}
    {Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ} (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    fracRelNormUnit k E Y ∈ coprimeToModulus k 𝔠 :=
  coe_raySymbol_gcop_eq_fracRelNormUnit' k E Y hY ▸ (raySymbol E (gcopNC2 k E 𝔠) _).2

def relNormCTM (𝔠 : Ideal (𝓞 k)) :
    ↥(coprimeToModulus E (modulusExt k E 𝔠)) →* ↥(coprimeToModulus k 𝔠) :=
  ((fracRelNormUnit k E).comp (coprimeToModulus E (modulusExt k E 𝔠)).subtype).codRestrict
    (coprimeToModulus k 𝔠) (fun Y => fracRelNormUnit_mem_coprimeToModulus k E Y.2)

end RelNorm

section Content

variable (K : Type*) [Field K] [NumberField K]


noncomputable def placeOf (τ : K →+* ℝ) : InfinitePlace K :=
  InfinitePlace.mk (Complex.ofRealHom.comp τ)

omit [NumberField K] in

theorem isReal_compOfRealHom (τ : K →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) :=
  RingHom.ext fun x => Complex.conj_ofReal (τ x)

omit [NumberField K] in
theorem isReal_placeOf (τ : K →+* ℝ) : (placeOf K τ).IsReal :=
  ⟨_, isReal_compOfRealHom K τ, rfl⟩

open InfinitePlace.Completion in

noncomputable def archRealProjTau (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : ℝ :=
  ringEquivRealOfIsReal (isReal_placeOf K τ)
    (((u : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) (placeOf K τ))

open InfinitePlace.Completion in

open InfinitePlace.Completion in

def archSign (τ : K →+* ℝ) (u : (AdeleRing (𝓞 K) K)ˣ) : Prop :=
  0 < archRealProjTau K τ u

open InfinitePlace.Completion in


structure IsAdjuster (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) : Prop where
  cong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) = 1 ∧
    Valued.v ((((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v - 1)
      ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))
  sign : ∀ τ : K →+* ℝ,
    archSign K τ (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)

end Content

end HeckeCharacter

namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter WithZero

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

def primeCarrier (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) : ↥(coprimeToModulus K 𝔣) :=
  ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩

def primeCarriers : Set ↥(coprimeToModulus K 𝔣) :=
  {x | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), x = primeCarrier K 𝔣 v hv}

end Carriers

section Inclusion

variable (K : Type*) [Field K] [NumberField K]

theorem coprimeToModulus_antitone {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : coprimeToModulus K 𝔪 ≤ coprimeToModulus K 𝔣 :=
  fun _ hx v hv => hx v (dvd_trans hv h)

noncomputable def ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : ↥(coprimeToModulus K 𝔪) →* ↥(coprimeToModulus K 𝔣) :=
  Subgroup.inclusion (coprimeToModulus_antitone K h)

end Inclusion

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N]
  [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]

def resHom : (N ≃ₐ[E] N) →* (M ≃ₐ[K] M) :=
  (AlgEquiv.restrictNormalHom M).comp
    { toFun := fun σ => σ.restrictScalars K
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }

end Tower

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

def admissibleExp (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal + 1

def IsAdmissibleModulus (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExp K v ∣ 𝔣

end Admissible

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


end DefN

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]


end Pincer

section UnitIdeles

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))


end UnitIdeles

structure ArtinFieldCore (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔣 : Ideal (𝓞 K)) (i : ↥(primeCarriers K 𝔣)) where
  E : Type*
  N : Type*
  Θ : Type*
  [instFE : Field E]
  [instNFE : NumberField E]
  [instFN : Field N]
  [instNFN : NumberField N]
  [instFΘ : Field Θ]
  [instNFΘ : NumberField Θ]
  [instAKE : Algebra K E]
  [instAKN : Algebra K N]
  [instAEN : Algebra E N]
  [instALN : Algebra L N]
  [instAEΘ : Algebra E Θ]
  [instANΘ : Algebra N Θ]
  [instSTKEN : IsScalarTower K E N]
  [instSTKLN : IsScalarTower K L N]
  [instSTENΘ : IsScalarTower E N Θ]
  [instGEN : IsGalois E N]
  [instGEΘ : IsGalois E Θ]
  [instCN : IsMulCommutative (N ≃ₐ[E] N)]
  [instCΘ : IsMulCommutative (Θ ≃ₐ[E] Θ)]
  𝔪 : Ideal (𝓞 K)
  h𝔪 : 𝔣 ∣ 𝔪
  v : HeightOneSpectrum (𝓞 K)
  hv𝔪 : ¬ v.asIdeal ∣ 𝔪
  hvi : primeCarrier K 𝔣 v (fun hv => hv𝔪 (dvd_trans hv h𝔪)) = (i : ↥(coprimeToModulus K 𝔣))
  w : HeightOneSpectrum (𝓞 E)
  hw : ¬ w.asIdeal ∣ modulusExt K E 𝔪
  hwv : w.asIdeal.under (𝓞 K) = v.asIdeal
  hf : v.asIdeal.inertiaDeg' w.asIdeal = 1
  q : ℕ
  [instNZq : NeZero q]
  ζ : Θ
  hζ : IsPrimitiveRoot ζ q
  htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤
  hq𝔪 : Ideal.span {(q : 𝓞 E)} ∣ modulusExt K E 𝔪
  hunr : ∀ v' : HeightOneSpectrum (𝓞 E), ¬ v'.asIdeal ∣ modulusExt K E 𝔪 →
    ((primeAbove E Θ v').under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥
  hadm : IsAdmissibleModulus E N (modulusExt K E 𝔪)
  hI_E : ∀ w' : HeightOneSpectrum (𝓞 E), ¬ w'.asIdeal ∣ modulusExt K E 𝔪 →
    ((primeAbove E N w').under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥
  hresInj : Function.Injective (resHom K L E N)

attribute [instance] ArtinFieldCore.instFE ArtinFieldCore.instNFE ArtinFieldCore.instFN
  ArtinFieldCore.instNFN ArtinFieldCore.instFΘ ArtinFieldCore.instNFΘ ArtinFieldCore.instAKE
  ArtinFieldCore.instAKN ArtinFieldCore.instAEN ArtinFieldCore.instALN ArtinFieldCore.instAEΘ
  ArtinFieldCore.instANΘ ArtinFieldCore.instSTKEN ArtinFieldCore.instSTKLN
  ArtinFieldCore.instSTENΘ ArtinFieldCore.instGEN ArtinFieldCore.instGEΘ ArtinFieldCore.instCN
  ArtinFieldCore.instCΘ ArtinFieldCore.instNZq

section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
  (c : ArtinFieldCore K L 𝔣 i)

def ArtinFieldCore.Ip : Type _ := ↥(coprimeToModulus c.E (modulusExt K c.E c.𝔪))


def ArtinFieldCore.ωpi : c.Ip →* (L ≃ₐ[K] L) :=
  (resHom K L c.E c.N).comp (artinSymbol c.E c.N (modulusExt K c.E c.𝔪))


end PerICore

structure ArtinPairCore (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔣 : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) {i j : ↥(primeCarriers K 𝔣)}
    (ci : ArtinFieldCore K L 𝔣 i) (cj : ArtinFieldCore K L 𝔣 j) where
  E'' : Type*
  N'' : Type*
  [instFE : Field E'']
  [instNFE : NumberField E'']
  [instFN : Field N'']
  [instNFN : NumberField N'']
  [instAKE : Algebra K E'']
  [instAKN : Algebra K N'']
  [instAiE : Algebra ci.E E'']
  [instAjE : Algebra cj.E E'']
  [instSTKiE : IsScalarTower K ci.E E'']
  [instSTKjE : IsScalarTower K cj.E E'']
  [instAEN : Algebra E'' N'']
  [instALN : Algebra L N'']
  [instSTKEN : IsScalarTower K E'' N'']
  [instSTKLN : IsScalarTower K L N'']
  [instGEN : IsGalois E'' N'']
  [instCN : IsMulCommutative (N'' ≃ₐ[E''] N'')]
  𝔪'' : Ideal (𝓞 K)
  h'' : 𝔣 ∣ 𝔪''
  hi'' : ci.𝔪 ∣ 𝔪''
  hj'' : cj.𝔪 ∣ 𝔪''
  hadm'' : IsAdmissibleModulus E'' N'' (modulusExt K E'' 𝔪'')
  hcompat'' : ∀ B : ↥(coprimeToModulus E'' (modulusExt K E'' 𝔪'')),
    artinSymbol K L 𝔣 (ctmInclusion K h'' (relNormCTM K E'' 𝔪'' B))
      = resHom K L E'' N'' (artinSymbol E'' N'' (modulusExt K E'' 𝔪'') B)
  hσ'' : σ ∈ (resHom K L E'' N'').range
  hresInj'' : Function.Injective (resHom K L E'' N'')

attribute [instance] ArtinPairCore.instFE ArtinPairCore.instNFE ArtinPairCore.instFN ArtinPairCore.instNFN
  ArtinPairCore.instAKE ArtinPairCore.instAKN ArtinPairCore.instAiE ArtinPairCore.instAjE ArtinPairCore.instSTKiE
  ArtinPairCore.instSTKjE ArtinPairCore.instAEN ArtinPairCore.instALN ArtinPairCore.instSTKEN ArtinPairCore.instSTKLN
  ArtinPairCore.instGEN ArtinPairCore.instCN

section IdeleData

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]


end IdeleData

section IdeleDataTop

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]


end IdeleDataTop

end LanglandsTunnell.P2.Artin
