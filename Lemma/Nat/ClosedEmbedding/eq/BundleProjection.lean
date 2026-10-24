import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.BorelWeil


/--
[SpringerResolutionData.closedEmbedding_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma SpringerResolutionData.closedEmbedding_eq
  {D : SpringerResolutionData}
  {y : D.CotangentBundle} :
-- imply
  D.closedEmbedding y = (D.bundleProjection y, D.springerMap y) :=
-- proof
  rfl

/--
[SpringerResolutionData.closedEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma SpringerResolutionData.closedEmbedding_injective
  {D : SpringerResolutionData} :
-- imply
  Function.Injective D.closedEmbedding := by
-- proof
  intro y₁ y₂ h
  simp only [closedEmbedding, Prod.mk.injEq] at h
  exact D.cotangentBundle_ext y₁ y₂ h.1 h.2

/--
[kirillovKostant_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma kirillovKostant_kernel
  {k : Type*}
  {𝔤 : Type*}
  [CommRing k]
  [LieRing 𝔤]
  [LieAlgebra k 𝔤]
  {f : 𝔤 →ₗ[k] k}
  {x : 𝔤} :
-- imply
  (∀ y : 𝔤, (kirillovKostantForm k 𝔤 f).bilin x y = 0) ↔ x ∈ coadjointStabilizer k 𝔤 f :=
-- proof
Iff.rfl

/--
[kirillovKostant_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma kirillovKostant_closed
  {k : Type*}
  {𝔤 : Type*}
  [CommRing k]
  [LieRing 𝔤]
  [LieAlgebra k 𝔤]
  {f : 𝔤 →ₗ[k] k}
  {x y z : 𝔤} :
-- imply
  f ⁅y, ⁅x, z⁆⁆ + f ⁅z, ⁅y, x⁆⁆ + f ⁅x, ⁅z, y⁆⁆ = 0 := by
-- proof
  have jacobi := lie_jacobi x z y
  have h := congr_arg f jacobi
  simp only [map_add, map_zero] at h
  set a := f ⁅x, ⁅z, y⁆⁆
  set b := f ⁅z, ⁅y, x⁆⁆
  set c := f ⁅y, ⁅x, z⁆⁆
  calc c + b + a = a + b + c := by ring
    _ = 0 := h

/--
[CoadjointOrbitData.mem_orbit_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma CoadjointOrbitData.mem_orbit_iff
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {data : CoadjointOrbitData k' 𝔤'}
  {f ξ : 𝔤' →ₗ[k'] k'} :
-- imply
  ξ ∈ data.orbit f ↔ ∃ g : data.G, data.coadjointAction g f = ξ := by
-- proof
  simp [CoadjointOrbitData.orbit, Set.mem_range]

/--
[CoadjointOrbitData.Ad_inv_cancel_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma CoadjointOrbitData.Ad_inv_cancel_left
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {data : CoadjointOrbitData k' 𝔤'}
  {g : data.G}
  {x : 𝔤'} :
-- imply
  (data.Ad g⁻¹) ((data.Ad g) x) = x := by
-- proof
  have h : data.Ad g⁻¹ * data.Ad g = 1 := by
    rw [← data.Ad.map_mul, inv_mul_cancel, data.Ad.map_one]
  calc (data.Ad g⁻¹) ((data.Ad g) x)
    = (data.Ad g⁻¹ * data.Ad g) x := (LinearEquiv.mul_apply _ _ _).symm
    _ = (1 : 𝔤' ≃ₗ[k'] 𝔤') x := by rw [h]
    _ = x := by simp

/--
[kirillovKostant_G_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma kirillovKostant_G_invariant
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {data : CoadjointOrbitData k' 𝔤'}
  {g : data.G}
  {f : 𝔤' →ₗ[k'] k'}
  {y z : 𝔤'} :
-- imply
  data.coadjointAction g f ⁅data.Ad g y, data.Ad g z⁆ = f ⁅y, z⁆ := by
-- proof
  rw [data.coadjoint_formula, ← data.Ad_preserves_bracket]
  congr 1
  exact data.Ad_inv_cancel_left g ⁅y, z⁆

/--
[kirillovKostant_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma kirillovKostant_symplectic
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {data : CoadjointOrbitData k' 𝔤'}
  {f : 𝔤' →ₗ[k'] k'} :
-- imply
  (∀ y z : 𝔤', f ⁅y, z⁆ = - f ⁅z, y⁆) ∧ (∀ x : 𝔤', (∀ y : 𝔤', f ⁅x, y⁆ = 0) ↔ x ∈ coadjointStabilizer k' 𝔤' f) ∧ (∀ (g : data.G) (y z : 𝔤'), data.coadjointAction g f ⁅data.Ad g y, data.Ad g z⁆ = f ⁅y, z⁆) ∧ (∀ x y z : 𝔤', f ⁅y, ⁅x, z⁆⁆ + f ⁅z, ⁅y, x⁆⁆ + f ⁅x, ⁅z, y⁆⁆ = 0) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro y z
    have := (kirillovKostantForm k' 𝔤' f).skew_symm y z
    simp only [kirillovKostantForm, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact this
  ·
    intro x
    exact kirillovKostant_kernel k' 𝔤' f x
  ·
    intro g y z
    exact kirillovKostant_G_invariant data g f y z
  ·
    intro x y z
    exact kirillovKostant_closed k' 𝔤' f x y z

/--
[even_sub_even_of_lt_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma even_sub_even_of_lt_ge_two
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {m n : ℕ}
-- given
  (hm : Even m)
  (hn : Even n)
  (hlt : n < m) :
-- imply
  m - n ≥ 2 := by
-- proof
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  omega

/--
[normalVariety_singular_locus_codim_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma normalVariety_singular_locus_codim_ge_two
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  [IsIntegrallyClosed R]
  {𝔭 : Ideal R}
  [𝔭.IsPrime]
-- given
  (h𝔭 : 𝔭.height = 1) :
-- imply
  IsRegularLocalRing (Localization.AtPrime 𝔭) := by
-- proof
  set S := Localization.AtPrime 𝔭
  haveI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 S]
    exact_mod_cast h𝔭
  have hunique : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime →
    P = IsLocalRing.maximalIdeal S := by
    intro P hP hPprime
    haveI := hPprime
    have hle := IsLocalRing.le_maximalIdeal (R := S) hPprime.ne_top
    by_contra hne
    have hlt : P < IsLocalRing.maximalIdeal S := lt_of_le_of_ne hle hne
    have h_bot_lt_P : (⊥ : Ideal S) < P := bot_lt_iff_ne_bot.mpr hP
    have h1 : (⊥ : Ideal S).primeHeight + 1 ≤ P.primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt h_bot_lt_P
    have h2 : P.primeHeight + 1 ≤ (IsLocalRing.maximalIdeal S).primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt hlt
    have h0 : (⊥ : Ideal S).primeHeight = 0 := by
      rw [Ideal.primeHeight_eq_zero_iff]
      rw [IsDomain.minimalPrimes_eq_singleton_bot]
      exact Set.mem_singleton _
    have hge2 : (IsLocalRing.maximalIdeal S).primeHeight ≥ 2 := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ P.primeHeight + 1 := by gcongr; rw [← h0]; exact h1
        _ ≤ (IsLocalRing.maximalIdeal S).primeHeight := h2
    have hmaxht : (IsLocalRing.maximalIdeal S).primeHeight = 1 := by
      have := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := S)
      rw [hdim] at this
      exact_mod_cast this
    rw [hmaxht] at hge2
    exact absurd hge2 (by norm_num)
  have hcond : IsIntegrallyClosed S ∧
    ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal S :=
    ⟨inferInstance, hunique⟩
  haveI : IsPrincipalIdealRing S :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 3 0).mp hcond
  exact IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing _

/--
[ResolutionData.pStar_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma ResolutionData.pStar_injective
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  [Field k]
  {R : ResolutionData k} :
-- imply
  Function.Injective R.pStar := by
-- proof
  obtain ⟨φ, hφ⟩ := R.hFracIso
  intro a b hab
  have ha := hφ a
  have hb := hφ b
  rw [hab] at ha
  rw [← hb] at ha
  exact IsFractionRing.injective R.OY (FractionRing R.OY) (φ.injective ha)

/--
[resolution_pullback_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma resolution_pullback_surjective
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  [Field k]
  {R : ResolutionData k} :
-- imply
  Function.Surjective R.pStar := by
-- proof
  letI : Algebra R.OY R.OX := R.pStar.toAlgebra
  intro f
  have hf : IsIntegral R.OY f := R.hProper.isIntegral f
  obtain ⟨φ, hφ⟩ := R.hFracIso
  let ψ : R.OX →+* FractionRing R.OY :=
    φ.symm.toRingHom.comp (algebraMap R.OX (FractionRing R.OX))
  have hcomp : (algebraMap R.OY (FractionRing R.OY)).comp (RingHom.id R.OY) =
    ψ.comp (algebraMap R.OY R.OX) := by
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply, ψ, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [show algebraMap R.OY R.OX r = R.pStar r from rfl, ← hφ r]
    simp [RingEquiv.symm_apply_apply]
  have hf_integral : IsIntegral R.OY (ψ f) :=
    hf.map_of_comp_eq (RingHom.id R.OY) ψ hcomp
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hf_integral
  refine ⟨y, ?_⟩
  have h1 : φ (algebraMap R.OY (FractionRing R.OY) y) =
    algebraMap R.OX (FractionRing R.OX) f := by
    rw [hy]
    simp only [ψ, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_coe, RingEquiv.apply_symm_apply]
  have h2 : algebraMap R.OX (FractionRing R.OX) (R.pStar y) =
    algebraMap R.OX (FractionRing R.OX) f := by
    rw [← hφ y, h1]
  exact IsFractionRing.injective R.OX (FractionRing R.OX) h2

/--
[resolution_pullback_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma resolution_pullback_isIso
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  [Field k]
  {R : ResolutionData k} :
-- imply
  Function.Bijective R.pStar :=
-- proof
  ⟨R.pStar_injective, resolution_pullback_surjective R⟩

/--
[graded_map_reflects_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma graded_map_reflects_mem
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  [Field k]
  [CommRing R]
  [Algebra k R]
  [CommRing S]
  [Algebra k S]
  {𝒜 : ℕ → Submodule k R}
  [GradedAlgebra 𝒜]
  {ℬ : ℕ → Submodule k S}
  [GradedAlgebra ℬ]
  {f : R →ₐ[k] S}
  {n : ℕ}
  {a : R}
-- given
  (hf_grade : ∀ n, ∀ a ∈ 𝒜 n, f a ∈ ℬ n)
  (hf_inj : Function.Injective f)
  (ha : f a ∈ ℬ n) :
-- imply
  a ∈ 𝒜 n := by
-- proof
  have naturality : ∀ (m : ℕ) (b : R),
    f (↑((DirectSum.decompose 𝒜 b) m)) = ↑((DirectSum.decompose ℬ (f b)) m) := by
    intro m b
    set 𝒜_sub := fun i => ↥(𝒜 i)
    let φ₁ : DirectSum ℕ 𝒜_sub →+ S :=
      { toFun := fun x => f (↑(x m) : R),
        map_zero' := by simp,
        map_add' := fun x y => by simp [DirectSum.add_apply, map_add] }
    let φ₂ : DirectSum ℕ 𝒜_sub →+ S :=
      { toFun := fun x => ↑((DirectSum.decompose ℬ (f ((DirectSum.decompose 𝒜).symm x))) m),
        map_zero' := by simp,
        map_add' := fun x y => by
          have hsymm := (DirectSum.decomposeAddEquiv 𝒜).symm.map_add x y
          simp only [DirectSum.decomposeAddEquiv_symm_apply] at hsymm
          rw [hsymm, map_add, DirectSum.decompose_add, DirectSum.add_apply]
          simp }
    have h_eq : φ₁ = φ₂ := DirectSum.addHom_ext (fun i y => by
      simp only [φ₁, φ₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, DirectSum.decompose_symm_of]
      by_cases him : i = m
      · subst him
        rw [DirectSum.of_eq_same]
        exact (DirectSum.decompose_of_mem_same ℬ (hf_grade _ (↑y) y.prop)).symm
      · have : (DirectSum.of 𝒜_sub i y) m = 0 :=
        DirectSum.of_eq_of_ne (β := 𝒜_sub) i m y (fun h => him (h.symm))
        rw [this, ZeroMemClass.coe_zero, map_zero]
        exact (DirectSum.decompose_of_mem_ne ℬ (hf_grade i (↑y) y.prop) him).symm)
    have := congr_fun (congr_arg DFunLike.coe h_eq) (DirectSum.decompose 𝒜 b)
    simp only [φ₁, φ₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rwa [Equiv.symm_apply_apply] at this
  suffices h_zero : ∀ m : ℕ, m ≠ n → (DirectSum.decompose 𝒜 a) m = 0 by
    suffices ha_eq : a = ↑((DirectSum.decompose 𝒜 a) n) by
      rw [ha_eq]; exact SetLike.coe_mem _
    apply (DirectSum.decompose 𝒜).injective
    rw [DirectSum.decompose_coe 𝒜 ((DirectSum.decompose 𝒜 a) n)]
    apply DFinsupp.ext; intro m
    by_cases hm : m = n
    · cases hm; rw [DirectSum.of_eq_same]
    · rw [h_zero m hm, DirectSum.of_eq_of_ne (β := fun i => ↥(𝒜 i)) n m _ hm]
  intro m hm
  have h1 : f (↑((DirectSum.decompose 𝒜 a) m)) = 0 := by
    rw [naturality m a, DirectSum.decompose_of_mem_ne ℬ ha (Ne.symm hm)]
  have h2 : (↑((DirectSum.decompose 𝒜 a) m) : R) = 0 := hf_inj (by rw [h1, map_zero])
  exact Subtype.val_injective h2

/--
[springer_pullback_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma springer_pullback_isIso
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  {D : SpringerResolutionData}
  {ON : Type*}
  [CommRing ON]
  [IsDomain ON]
  [Algebra D.k ON]
  [IsIntegrallyClosed ON]
  [IsNoetherianRing ON]
  {𝒩_grade : ℕ → Submodule D.k ON}
  [GradedAlgebra 𝒩_grade]
  {OTF : Type*}
  [CommRing OTF]
  [IsDomain OTF]
  [Algebra D.k OTF]
  {TF_grade : ℕ → Submodule D.k OTF}
  [GradedAlgebra TF_grade]
  {pstar : ON →ₐ[D.k] OTF}
-- given
  (hbirational : ∃ (φ : FractionRing ON ≃+* FractionRing OTF), ∀ r : ON, φ (algebraMap ON (FractionRing ON) r) = algebraMap OTF (FractionRing OTF) (pstar r))
  (hproper : letI : Algebra ON OTF := pstar.toRingHom.toAlgebra; Algebra.IsIntegral ON OTF)
  (hpstar_preserves_grade : ∀ n : ℕ, ∀ f : ON, f ∈ 𝒩_grade n → pstar f ∈ TF_grade n) :
-- imply
  ∃ (e : ON ≃ₐ[D.k] OTF), (∀ f : ON, e f = pstar f) ∧ IsGradedAlgEquiv 𝒩_grade TF_grade e := by
-- proof
  let RD : ResolutionData D.k :=
    { OY := ON
      OX := OTF
      pStar := pstar.toRingHom
      hProper := hproper
      hFracIso := hbirational }
  have hbij : Function.Bijective pstar := resolution_pullback_isIso RD
  refine ⟨AlgEquiv.ofBijective pstar hbij,
    fun f => AlgEquiv.ofBijective_apply pstar hbij f,
    fun n a => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  constructor
  ·
    exact hpstar_preserves_grade n a
  ·
    exact graded_map_reflects_mem 𝒩_grade TF_grade pstar hpstar_preserves_grade hbij.1 n a

/--
[nilpotentCone_coordRing_isDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean)
-/
@[path]
private lemma nilpotentCone_coordRing_isDomain_eq
  [CommRing k']
  [LieRing 𝔤']
  [LieAlgebra k' 𝔤']
  [Field k]
  [LieRing 𝔤]
  [LieAlgebra k 𝔤]
  [LieAlgebra.IsSemisimple k 𝔤]
  [Module.Finite k 𝔤]
  {D : NilpotentConeCoordRingData k 𝔤} :
-- imply
  IsDomain D.coordRing := by
-- proof
  apply nilpotentCone_coordRing_isDomain D


-- created on 2026-10-24
