import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
open RayClassField
open scoped NumberField


namespace RayClassField

/--
[Modulus.infSupport_subset_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma Modulus.infSupport_subset_real
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  ∀ v ∈ 𝔪.infSupport, v.IsReal := by
-- proof
  intro v hv
  exact (NumberField.InfinitePlace.not_isComplex_iff_isReal).mp
    (fun hc => hv (𝔪.complex_zero v hc))

end RayClassField

namespace RayClassField

/--
[artinMap_at_prime_eq_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma artinMap_at_prime_eq_frobenius
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [KroneckerWeber.IsAbelianExtension K L]
  {𝔪 : Modulus K}
  {𝔭 : FinitePlace K}
-- given
  (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭) = FrobeniusAutomorphism K L 𝔭 :=
-- proof
  (artinMapExists K L 𝔪).choose_spec 𝔭 h𝔭

end RayClassField

namespace RayClassField

/--
[restrictNormalHom_isArithFrobAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma restrictNormalHom_isArithFrobAt
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [IsGalois K L]
  [IsGalois K M]
  [IsScalarTower K L M]
  {Q_M : Ideal (NumberField.RingOfIntegers M)}
  [Q_M.IsPrime]
  [Finite (NumberField.RingOfIntegers M ⧸ Q_M)]
  {σ : M ≃ₐ[K] M}
-- given
  (hσ : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q_M) :
-- imply
  IsArithFrobAt (NumberField.RingOfIntegers K) (AlgEquiv.restrictNormalHom L σ) (Q_M.comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) := by
-- proof
  intro y
  rw [Ideal.mem_comap, map_sub, map_pow]
  have hunder : (Q_M.comap (algebraMap (NumberField.RingOfIntegers L)
    (NumberField.RingOfIntegers M))).under (NumberField.RingOfIntegers K)
    = Q_M.under (NumberField.RingOfIntegers K) := by
    simp only [Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [hunder]
  have compat : (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))
    ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
      (AlgEquiv.restrictNormalHom L σ)) y) =
    (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers M) σ)
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M) y) := by
    ext
    exact AlgEquiv.restrictNormal_commutes σ L ↑y
  rw [compat]
  exact hσ (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M) y)

end RayClassField

namespace RayClassField

/--
[choosePrimeOver_comap_over](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma choosePrimeOver_comap_over
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [IsGalois K L]
  [IsGalois K M]
  [IsScalarTower K L M]
  {𝔭 : FinitePlace K} :
-- imply
  ((choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).comap (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal := by
-- proof
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, choosePrimeOver_over]

end RayClassField

namespace RayClassField

/--
[prop_7_13_restrictNormalHom_arithFrobAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma prop_7_13_restrictNormalHom_arithFrobAt
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [IsGalois K L]
  [IsGalois K M]
  [IsScalarTower K L M]
  {𝔭 : FinitePlace K}
  [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) ((choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))] :
-- imply
  (AlgEquiv.restrictNormalHom L) (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) (choosePrimeOver K M 𝔭)) = arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) ((choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) := by
-- proof
  set Q_M := choosePrimeOver K M 𝔭
  set Q_L := Q_M.comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))
  have h_lhs : IsArithFrobAt (NumberField.RingOfIntegers K)
    ((AlgEquiv.restrictNormalHom L)
      (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)) Q_L :=
    restrictNormalHom_isArithFrobAt K L M Q_M
      (arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)
      (IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (M ≃ₐ[K] M) Q_M)
  have h_rhs : IsArithFrobAt (NumberField.RingOfIntegers K)
    (arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q_L) Q_L :=
    IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q_L
  have hQ : Q_L.primeCompl ≤ nonZeroDivisors (NumberField.RingOfIntegers L) :=
    Ideal.primeCompl_le_nonZeroDivisors Q_L
  exact MulSemiringAction.toAlgHom_injective
    (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
    (h_lhs.eq_of_isUnramifiedAt h_rhs hQ)

end RayClassField

namespace RayClassField

/--
[arithFrobAt_eq_of_under_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma arithFrobAt_eq_of_under_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  [KroneckerWeber.IsAbelianExtension K L]
  {Q Q' : Ideal (NumberField.RingOfIntegers L)}
  [Q.IsPrime]
  [Finite (NumberField.RingOfIntegers L ⧸ Q)]
  [Q'.IsPrime]
  [Finite (NumberField.RingOfIntegers L ⧸ Q')]
-- given
  (h : Q.under (NumberField.RingOfIntegers K) = Q'.under (NumberField.RingOfIntegers K)) :
-- imply
  arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q = arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q' := by
-- proof
  have hconj := isConj_arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q Q' h
  exact hconj.eq_of_left_mem_center
    (Semigroup.mem_center_iff.mpr (fun x =>
      (KroneckerWeber.IsAbelianExtension.comm _ x).symm))

end RayClassField

namespace RayClassField

/--
[restrictNormalHom_frobeniusAutomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma restrictNormalHom_frobeniusAutomorphism
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [IsGalois K L]
  [IsGalois K M]
  [IsScalarTower K L M]
  [KroneckerWeber.IsAbelianExtension K L]
  {𝔭 : FinitePlace K}
  [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) ((choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))] :
-- imply
  (AlgEquiv.restrictNormalHom L) (FrobeniusAutomorphism K M 𝔭) = FrobeniusAutomorphism K L 𝔭 := by
-- proof
  unfold FrobeniusAutomorphism
  rw [prop_7_13_restrictNormalHom_arithFrobAt K L M 𝔭]
  exact arithFrobAt_eq_of_under_eq K L _ _ (by
    simp only [Ideal.under_def]
    rw [choosePrimeOver_comap_over K L M 𝔭, choosePrimeOver_over K L 𝔭])

end RayClassField

namespace RayClassField

/--
[prop_7_22_artinMap_at_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma prop_7_22_artinMap_at_prime
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [KroneckerWeber.IsAbelianExtension K L]
  [KroneckerWeber.IsAbelianExtension K M]
  [IsScalarTower K L M]
  {𝔪 : Modulus K}
  {𝔭 : FinitePlace K}
  [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) ((choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))]
-- given
  (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  (AlgEquiv.restrictNormalHom L) (ArtinMap K M 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭)) = ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h𝔭) := by
-- proof
  rw [artinMap_at_prime_eq_frobenius K M 𝔪 𝔭 h𝔭,
    artinMap_at_prime_eq_frobenius K L 𝔪 𝔭 h𝔭]
  exact restrictNormalHom_frobeniusAutomorphism K L M 𝔭

end RayClassField

namespace RayClassField

/--
[proposition_21_1_artin_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma proposition_21_1_artin_commutes
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [KroneckerWeber.IsAbelianExtension K L]
  [KroneckerWeber.IsAbelianExtension K M]
  [IsScalarTower K L M]
  {𝔪 : Modulus K}
  {I : FracIdealsCoprime K 𝔪}
-- given
  (hdiv : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 𝔪 (Place.finite 𝔭) = 0 → ∀ (𝔔 : Ideal (𝓞 L)) [𝔔.IsPrime], 𝔔.LiesOver 𝔭.asIdeal → Algebra.IsUnramifiedAt (𝓞 K) 𝔔) :
-- imply
  (AlgEquiv.restrictNormalHom L) (ArtinMap K M 𝔪 I) = ArtinMap K L 𝔪 I := by
-- proof
  have heq : (AlgEquiv.restrictNormalHom L).comp (ArtinMap K M 𝔪) = ArtinMap K L 𝔪 := by
    apply MonoidHom.eq_of_eqOn_dense (fracIdealsCoprime_closure_primes K 𝔪)
    intro x hx
    obtain ⟨𝔭, h𝔭, rfl⟩ := hx
    haveI : Algebra.IsUnramifiedAt (𝓞 K)
      ((choosePrimeOver K M 𝔭).comap (algebraMap (𝓞 L) (𝓞 M))) :=
      hdiv 𝔭 h𝔭 _ (Ideal.LiesOver.mk ((choosePrimeOver_comap_over K L M 𝔭).symm ▸
        (Ideal.under_def (𝓞 K) _).symm))
    exact prop_7_22_artinMap_at_prime K L M 𝔪 𝔭 h𝔭
  exact DFunLike.congr_fun heq I

end RayClassField

namespace RayClassField

/--
[exactSeq_exact_at_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma exactSeq_exact_at_units
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  MonoidHom.range (exactSeq_map1 𝔪) = MonoidHom.ker (exactSeq_map2 𝔪) := by
-- proof
  ext u
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨x, rfl⟩
    show (exactSeq_map2 𝔪) ((exactSeq_map1 𝔪) x) = 1
    change ((QuotientGroup.mk' (UnitsCongruent_in_UnitsCoprime K 𝔪)).comp
      (okUnitsToUnitsCoprime 𝔪)) ((UnitsInCongruenceSubgroup_subgroup K 𝔪).subtype x) = 1
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]
    have hx := x.property
    exact Subgroup.mem_comap.mp hx
  ·
    intro h_ker
    have h_ker' : ((QuotientGroup.mk' (UnitsCongruent_in_UnitsCoprime K 𝔪)).comp
      (okUnitsToUnitsCoprime 𝔪)) u = 1 := h_ker
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h_ker'
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf] at h_ker'
    refine ⟨⟨u, ?_⟩, rfl⟩
    rw [UnitsInCongruenceSubgroup_subgroup, Subgroup.mem_comap]
    convert h_ker' using 1

end RayClassField

namespace RayClassField

/--
[toPrincipalIdeal_algebraMap_unit'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma toPrincipalIdeal_algebraMap_unit'
  [Field K]
  [NumberField K]
  {u : (NumberField.RingOfIntegers K)ˣ} :
-- imply
  toPrincipalIdeal (NumberField.RingOfIntegers K) K (Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom u) = 1 := by
-- proof
  apply Units.ext
  rw [Units.val_one, coe_toPrincipalIdeal]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨u⁻¹, by simp [Units.smul_def, Algebra.smul_def]⟩

end RayClassField

namespace RayClassField

/--
[principalIdealMap_okUnitsToUnitsCoprime_eq_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma principalIdealMap_okUnitsToUnitsCoprime_eq_one'
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {u : (NumberField.RingOfIntegers K)ˣ} :
-- imply
  principalIdealMap 𝔪 (okUnitsToUnitsCoprime 𝔪 u) = 1 := by
-- proof
  apply Subtype.ext
  exact toPrincipalIdeal_algebraMap_unit' u

end RayClassField

namespace RayClassField

/--
[toPrincipalIdeal_eq_exists_unit'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma toPrincipalIdeal_eq_exists_unit'
  [Field K]
  [NumberField K]
  {x y : Kˣ}
-- given
  (h : toPrincipalIdeal (NumberField.RingOfIntegers K) K x = toPrincipalIdeal (NumberField.RingOfIntegers K) K y) :
-- imply
  ∃ u : (NumberField.RingOfIntegers K)ˣ, x = Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom u * y := by
-- proof
  have h1 : toPrincipalIdeal (NumberField.RingOfIntegers K) K (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 : (toPrincipalIdeal (NumberField.RingOfIntegers K) K (x * y⁻¹) :
    FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) = 1 := by
    rw [h1]; simp
  rw [coe_toPrincipalIdeal, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨z⁻¹, ?_⟩
  have hz_units : Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z *
    (x * y⁻¹) = 1 := by
    ext
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_inv_eq_inv_val, Units.val_one]
    rw [Units.smul_def, Algebra.smul_def] at hz
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hz
    exact hz
  have hxy : x * y⁻¹ =
    Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z⁻¹ :=
    mul_left_cancel
      (a := Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z)
      (by rw [hz_units, ← map_mul]; simp)
  calc x = (x * y⁻¹) * y := by group
    _ = Units.map (algebraMap (NumberField.RingOfIntegers K) K).toMonoidHom z⁻¹ * y := by rw [hxy]

end RayClassField

namespace RayClassField

/--
[rayGroup_le_map_congruent'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma rayGroup_le_map_congruent'
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  RayGroup K 𝔪 ≤ Subgroup.map (principalIdealMap 𝔪) (UnitsCongruent_in_UnitsCoprime K 𝔪) := by
-- proof
  rw [RayGroup, Subgroup.closure_le]
  intro I hI
  obtain ⟨α, hI_eq, hI_cong, hI_sign⟩ := hI
  have hα_coprime : α ∈ UnitsCoprime_subgroup' K 𝔪 := by
    intro v hv
    have hI_cop := I.property v hv
    have hI_val_eq : I.val = toPrincipalIdeal (NumberField.RingOfIntegers K) K α := by
      apply Units.val_injective
      rwa [coe_toPrincipalIdeal]
    rw [hI_val_eq] at hI_cop
    exact valuation_eq_one_of_spanSingleton_coprime' v α hI_cop.1 hI_cop.2
  set γ : UnitsCoprime_subgroup' K 𝔪 := ⟨α, hα_coprime⟩
  have hγ_cong : γ ∈ UnitsCongruent_in_UnitsCoprime K 𝔪 := by
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]
    exact ⟨hα_coprime, hI_cong, hI_sign⟩
  have hγ_eq : principalIdealMap 𝔪 γ = I := by
    apply Subtype.ext
    apply Units.val_injective
    simp only [principalIdealMap, MonoidHom.coe_mk, OneHom.coe_mk, coe_toPrincipalIdeal]
    exact hI_eq.symm
  exact ⟨γ, hγ_cong, hγ_eq⟩

end RayClassField

namespace RayClassField

/--
[exactSeq_exact_at_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma exactSeq_exact_at_quotient
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  MonoidHom.range (exactSeq_map2 𝔪) = MonoidHom.ker (exactSeq_map3 𝔪) := by
-- proof
  ext ⟨α⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨u, hu⟩
    rw [← hu]
    show exactSeq_map3 𝔪 (exactSeq_map2 𝔪 u) = 1
    simp only [exactSeq_map2, exactSeq_map3]
    erw [QuotientGroup.lift_mk']
    show (QuotientGroup.mk' (RayGroup K 𝔪)) (principalIdealMap 𝔪 ((okUnitsToUnitsCoprime 𝔪) u)) = 1
    rw [principalIdealMap_okUnitsToUnitsCoprime_eq_one' 𝔪 u, map_one]
  ·
    intro h
    have h_mem : principalIdealMap 𝔪 α ∈ RayGroup K 𝔪 := by
      rw [← QuotientGroup.eq_one_iff]
      have key : (exactSeq_map3 𝔪)
        (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α) =
        ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) α := by
        simp only [exactSeq_map3]
        erw [QuotientGroup.lift_mk']
      simp only [MonoidHom.comp_apply] at key
      have h1 : (QuotientGroup.mk' (RayGroup K 𝔪)) (principalIdealMap 𝔪 α) = 1 := by
        rw [← key]; exact h
      rwa [QuotientGroup.mk'_apply] at h1
    have hmap := rayGroup_le_map_congruent' 𝔪 h_mem
    rw [Subgroup.mem_map] at hmap
    obtain ⟨β, hβ_cong, hβ_eq⟩ := hmap
    have h_topi : toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ) =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K (β : Kˣ) := by
      have := congr_arg Subtype.val hβ_eq
      exact this.symm
    obtain ⟨u, hu⟩ := toPrincipalIdeal_eq_exists_unit' (α : Kˣ) (β : Kˣ) h_topi
    refine ⟨u, ?_⟩
    simp only [exactSeq_map2]
    erw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [UnitsCongruent_in_UnitsCoprime, Subgroup.mem_subgroupOf]
    have hval : (((okUnitsToUnitsCoprime 𝔪 u)⁻¹ * α : ↥(UnitsCoprime_subgroup' K 𝔪)) : Kˣ) =
      (β : Kˣ) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show (okUnitsToKUnits u)⁻¹ * (α : Kˣ) = (β : Kˣ)
      rw [hu]
      simp [okUnitsToKUnits]
    rw [show (((okUnitsToUnitsCoprime 𝔪 u)⁻¹ * α : ↥(UnitsCoprime_subgroup' K 𝔪)) : Kˣ) =
      (β : Kˣ) from hval]
    exact Subgroup.mem_subgroupOf.mp hβ_cong

end RayClassField

namespace RayClassField

/--
[corollary_21_9_ray_class_number](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma corollary_21_9_ray_class_number
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Nat.card (RayClassGroup K 𝔪) * (UnitsInCongruenceSubgroup_subgroup K 𝔪).index = Nat.card (SignsTimesUnits K 𝔪) * Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
-- proof
  have h_index_f2 : (exactSeq_map2 𝔪).ker.index = Nat.card (exactSeq_map2 𝔪).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (exactSeq_map2 𝔪)).toEquiv
  have h_ker2_eq_H : (exactSeq_map2 𝔪).ker = UnitsInCongruenceSubgroup_subgroup K 𝔪 := by
    rw [← exactSeq_exact_at_units 𝔪]
    exact (UnitsInCongruenceSubgroup_subgroup K 𝔪).range_subtype
  have h_ker3_eq_range2 : Nat.card (↥(exactSeq_map3 𝔪).ker) =
    Nat.card (↥(exactSeq_map2 𝔪).range) := by
    congr 1; rw [exactSeq_exact_at_quotient 𝔪]
  have h_lagrange_QU : Nat.card (↥(exactSeq_map3 𝔪).ker) * (exactSeq_map3 𝔪).ker.index =
    Nat.card (QuotientUnits K 𝔪) :=
    Subgroup.card_mul_index (exactSeq_map3 𝔪).ker
  have h_index_f3 : (exactSeq_map3 𝔪).ker.index = Nat.card (exactSeq_map3 𝔪).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (exactSeq_map3 𝔪)).toEquiv
  have h_lagrange_RCG : Nat.card (↥(exactSeq_map4 𝔪).ker) * (exactSeq_map4 𝔪).ker.index =
    Nat.card (RayClassGroup K 𝔪) :=
    Subgroup.card_mul_index (exactSeq_map4 𝔪).ker
  have h_ker4_eq_range3 : Nat.card (↥(exactSeq_map4 𝔪).ker) =
    Nat.card (↥(exactSeq_map3 𝔪).range) := by
    congr 1; rw [exactSeq_exact_at_ray_class 𝔪]
  have h_index_f4 : (exactSeq_map4 𝔪).ker.index =
    Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rwa [Subgroup.index_eq_card]
      (QuotientGroup.quotientKerEquivOfSurjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv
  have h_iso : Nat.card (QuotientUnits K 𝔪) = Nat.card (SignsTimesUnits K 𝔪) :=
    Nat.card_congr (Classical.choice (theorem_21_8_quotient_iso 𝔪)).toEquiv
  have h_RCG : Nat.card (RayClassGroup K 𝔪) =
    Nat.card (↥(exactSeq_map3 𝔪).range) * Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rw [← h_lagrange_RCG, h_ker4_eq_range3, h_index_f4]
  have h_QU : Nat.card (QuotientUnits K 𝔪) =
    Nat.card (↥(exactSeq_map2 𝔪).range) * Nat.card (↥(exactSeq_map3 𝔪).range) := by
    rw [← h_lagrange_QU, h_ker3_eq_range2, h_index_f3]
  have h_STU : Nat.card (SignsTimesUnits K 𝔪) =
    Nat.card (↥(exactSeq_map2 𝔪).range) * Nat.card (↥(exactSeq_map3 𝔪).range) := by
    rw [← h_iso, h_QU]
  rw [h_RCG, ← h_ker2_eq_H, h_index_f2, h_STU]
  ring

end RayClassField

namespace RayClassField

/--
[corollary_21_9_class_dvd_ray](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma corollary_21_9_class_dvd_ray
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) ∣ Fintype.card (RayClassGroup K 𝔪) := by
-- proof
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)

end RayClassField

namespace RayClassField

/--
[corollary_21_9_ray_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma corollary_21_9_ray_dvd
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Fintype.card (RayClassGroup K 𝔪) ∣ Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) * Fintype.card (SignsTimesUnits K 𝔪) := by
-- proof
  simp only [← Nat.card_eq_fintype_card]
  have hcard_iso : Nat.card (QuotientUnits K 𝔪) = Nat.card (SignsTimesUnits K 𝔪) :=
    Nat.card_congr (Classical.choice (theorem_21_8_quotient_iso 𝔪)).toEquiv
  have h_card_eq : Nat.card (↥(exactSeq_map4 𝔪).ker) * (exactSeq_map4 𝔪).ker.index =
    Nat.card (RayClassGroup K 𝔪) := Subgroup.card_mul_index _
  have h_index : (exactSeq_map4 𝔪).ker.index =
    Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rwa [Subgroup.index]
      (QuotientGroup.quotientKerEquivOfSurjective (exactSeq_map4 𝔪) (exactSeq_surjective 𝔪)).toEquiv
  have h_range_dvd : Nat.card (↥(exactSeq_map3 𝔪).range) ∣ Nat.card (QuotientUnits K 𝔪) :=
    Subgroup.card_range_dvd (exactSeq_map3 𝔪)
  have h_ker_range : Nat.card (↥(exactSeq_map4 𝔪).ker) =
    Nat.card (↥(exactSeq_map3 𝔪).range) := by
    have : ↥(exactSeq_map4 𝔪).ker = ↥(exactSeq_map3 𝔪).range := by
      rw [exactSeq_exact_at_ray_class 𝔪]
    rw [this]
  rw [← h_card_eq, h_index, h_ker_range, mul_comm]
  exact mul_dvd_mul_left _ (h_range_dvd.trans (dvd_of_eq hcard_iso))

end RayClassField

namespace RayClassField

/--
[corollary_21_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma corollary_21_9
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  (Nat.card (RayClassGroup K 𝔪) * (UnitsInCongruenceSubgroup_subgroup K 𝔪).index = Nat.card (SignsTimesUnits K 𝔪) * Nat.card (ClassGroup (NumberField.RingOfIntegers K))) ∧ (Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) ∣ Fintype.card (RayClassGroup K 𝔪)) ∧ (Fintype.card (RayClassGroup K 𝔪) ∣ Fintype.card (ClassGroup (NumberField.RingOfIntegers K)) * Fintype.card (SignsTimesUnits K 𝔪)) :=
-- proof
  ⟨corollary_21_9_ray_class_number 𝔪,
    corollary_21_9_class_dvd_ray 𝔪,
    corollary_21_9_ray_dvd 𝔪⟩

end RayClassField

namespace RayClassField

/--
[eulerFactor_analyticAt_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma eulerFactor_analyticAt_one
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {𝔭 : Prime' K} :
-- imply
  AnalyticAt ℂ (fun s : ℂ => (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹) 1 := by
-- proof
  have hne : (Ideal.absNorm 𝔭.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Ideal.absNorm_ne_zero_iff _).mpr
      (𝔭.asIdeal.finiteQuotientOfFreeOfNeBot 𝔭.ne_bot))
  apply AnalyticAt.inv
  · apply AnalyticAt.sub analyticAt_const
    have hrw : ∀ s : ℂ, (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s) =
      Complex.exp (-s * Complex.log (Ideal.absNorm 𝔭.asIdeal : ℂ)) := by
      intro s; rw [Complex.cpow_def_of_ne_zero hne]; ring_nf
    simp_rw [hrw]
    exact ((analyticAt_id (𝕜 := ℂ)).neg.mul analyticAt_const).cexp
  · rw [sub_ne_zero]; intro h
    rw [show (-(1 : ℂ)) = ((-1 : ℤ) : ℂ) from by push_cast; ring,
      Complex.cpow_intCast, zpow_neg_one] at h
    have h3 : Ideal.absNorm 𝔭.asIdeal = 1 := by exact_mod_cast (inv_eq_one.mp h.symm)
    have hmax := IsDedekindDomain.HeightOneSpectrum.isMaximal 𝔭
    haveI := 𝔭.asIdeal.finiteQuotientOfFreeOfNeBot 𝔭.ne_bot
    haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
    haveI := (Ideal.Quotient.nontrivial_iff (I := 𝔭.asIdeal)).mpr hmax.ne_top
    have h5 : 1 < Fintype.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
      Fintype.one_lt_card
    have h6 : Ideal.absNorm 𝔭.asIdeal =
      Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := rfl
    rw [h6, Nat.card_eq_fintype_card] at h3
    linarith

end RayClassField

namespace RayClassField

/--
[hasDirichletDensity_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma hasDirichletDensity_unique
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ₁ ρ₂ : ℚ}
-- given
  (h₁ : HasDirichletDensity K S ρ₁)
  (h₂ : HasDirichletDensity K S ρ₂) :
-- imply
  ρ₁ = ρ₂ := by
-- proof
  exact_mod_cast tendsto_nhds_unique h₁ h₂

end RayClassField

namespace RayClassField

/--
[hasNaturalDensity_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma hasNaturalDensity_unique
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ₁ ρ₂ : ℚ}
-- given
  (h₁ : HasNaturalDensity K S ρ₁)
  (h₂ : HasNaturalDensity K S ρ₂) :
-- imply
  ρ₁ = ρ₂ := by
-- proof
  exact_mod_cast tendsto_nhds_unique h₁ h₂

end RayClassField

namespace RayClassField

/--
[meromorphic_poleOrder_realLog_limit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma meromorphic_poleOrder_realLog_limit
  [Field K]
  [NumberField K]
  {f : ℂ → ℂ}
  {m : ℤ}
-- given
  (hm : HasMeromorphicContinuationWithPoleOrder f m) :
-- imply
  ∃ C : ℝ, Filter.Tendsto (fun s : ℝ => Real.log ‖f ((s : ℂ))‖ + (m : ℝ) * Real.log (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by
-- proof
  obtain ⟨hmer, hord⟩ := hm
  rw [meromorphicOrderAt_eq_int_iff hmer] at hord
  obtain ⟨g, hg_an, hg_ne, hf_eq⟩ := hord
  refine ⟨Real.log ‖g 1‖, ?_⟩
  have hg_lim : Filter.Tendsto (fun s : ℝ => Real.log ‖g ((s : ℂ))‖)
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log ‖g 1‖)) := by
    have h_gR : ContinuousAt (fun s : ℝ => g ((s : ℂ))) 1 :=
      hg_an.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
    exact ((continuous_norm.continuousAt.comp h_gR).log (by simp [hg_ne])).continuousWithinAt.tendsto
  apply Filter.Tendsto.congr'
  ·
    have hf_eq_R : ∀ᶠ (s : ℝ) in nhdsWithin 1 (Set.Ioi 1),
      f (↑s) = ((↑s - 1 : ℂ)) ^ (-m) • g (↑s) := by
      rw [Filter.Eventually, mem_nhdsWithin] at hf_eq ⊢
      obtain ⟨U, hU_open, h1U, hUprop⟩ := hf_eq
      refine ⟨Complex.ofReal ⁻¹' U, hU_open.preimage Complex.continuous_ofReal,
        by simp [h1U], ?_⟩
      intro s ⟨hsU, hs_ioi⟩
      exact hUprop ⟨hsU, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact fun h => absurd (Complex.ofReal_injective h) (ne_of_gt hs_ioi)⟩
    have hg_ne_R : ∀ᶠ (s : ℝ) in nhdsWithin 1 (Set.Ioi 1), g (↑s) ≠ 0 := by
      have h_gR : ContinuousAt (fun s : ℝ => g ((s : ℂ))) 1 :=
        hg_an.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
      have : (fun s : ℝ => g ((s : ℂ))) 1 = g 1 := by simp
      exact (h_gR.eventually (this ▸ isOpen_ne.mem_nhds hg_ne)).filter_mono nhdsWithin_le_nhds
    show (fun s : ℝ => Real.log ‖g ((s : ℂ))‖) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ => Real.log ‖f ((s : ℂ))‖ + (m : ℝ) * Real.log (s - 1))
    filter_upwards [hf_eq_R, hg_ne_R,
      eventually_nhdsWithin_of_forall (fun s (hs : s ∈ Set.Ioi 1) => hs)]
      with s hf_s hg_s hs1
    have hs1' : 1 < s := hs1
    rw [hf_s, norm_smul, norm_zpow]
    have hs1_eq : ‖(↑s - 1 : ℂ)‖ = s - 1 := by
      rw [show (↑s - 1 : ℂ) = ↑(s - 1) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hs1_eq]
    have hs1_pos : (0 : ℝ) < s - 1 := by linarith
    rw [Real.log_mul (zpow_ne_zero _ (ne_of_gt hs1_pos)) (norm_ne_zero_iff.mpr hg_s)]
    rw [Real.log_zpow]
    push_cast; ring
  · exact hg_lim

end RayClassField

namespace RayClassField

/--
[card_primes_le_card_ideals'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma card_primes_le_card_ideals'
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {n : ℕ} :
-- imply
  Nat.card {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
-- proof
  Nat.card_le_card_of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

end RayClassField

namespace RayClassField

/--
[ideal_count_rpow_summable'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma ideal_count_rpow_summable'
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ (-σ))) := by
-- proof
  have hLS : LSeriesSummable
    (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one
    · simp; exact hσ
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
      (a := NumberField.dedekindZeta_residue K)
    simp only [Real.rpow_one]
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]; congr 1; norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  exact (hLS.norm).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [LSeries.norm_term_eq]; split_ifs with h
    · subst h
      simp [Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < σ)))]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n)])

end RayClassField

namespace RayClassField

/--
[summable_primeIdeal_absNorm_rpow'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma summable_primeIdeal_absNorm_rpow'
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ)) := by
-- proof
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : Prime' K =>
    Ideal.absNorm 𝔭.asIdeal)).summable_iff]
  suffices h : Summable (fun p : (n : ℕ) × {𝔭 : Prime' K //
    Ideal.absNorm 𝔭.asIdeal = n} => ((p.1 : ℝ) ^ (-σ))) by
    exact h.congr (fun ⟨n, 𝔭, h⟩ => by
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      congr 1; exact_mod_cast h.symm)
  rw [summable_sigma_of_nonneg (fun ⟨n, _⟩ => by positivity)]
  exact ⟨fun n => Summable.of_finite, by
    simp_rw [tsum_const, nsmul_eq_mul]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_primes_le_card_ideals' K n) (by positivity))
      (ideal_count_rpow_summable' K σ hσ)⟩

end RayClassField

namespace RayClassField

variable [Field K] [NumberField K]
/--
[norm_inv_one_sub_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma norm_inv_one_sub_sub_one {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
  ‖(1 - a)⁻¹ - 1‖ ≤ 2 * ‖a‖ := by
  by_cases ha0 : a = 0; · simp [ha0]
  have ha1 : ‖a‖ < 1 := by linarith
  have h1a : (1 : ℂ) - a ≠ 0 := by
    intro h; have := sub_eq_zero.mp h; rw [← this] at ha1; simp at ha1
  rw [show (1 - a)⁻¹ - 1 = a * (1 - a)⁻¹ from by field_simp; ring,
    norm_mul, norm_inv]
  calc ‖a‖ * ‖(1 : ℂ) - a‖⁻¹
    ≤ ‖a‖ * (1 - ‖a‖)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (by linarith)
          (by linarith [norm_sub_norm_le (1 : ℂ) a, norm_one (α := ℂ)]))
        (norm_nonneg a)
    _ ≤ ‖a‖ * (1 / 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (by linarith : (0 : ℝ) < 1 / 2) (by linarith)) (norm_nonneg a)
    _ = 2 * ‖a‖ := by ring

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_multipliable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_multipliable
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  Multipliable (fun (𝔭 : S) => (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) := by
-- proof
  have key : (fun (𝔭 : S) =>
    (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) =
    (fun (𝔭 : S) => 1 + ((1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹ - 1)) := by
    ext; ring
  rw [key]
  apply Complex.multipliable_one_add_of_summable
  apply Summable.of_norm
  have hre : (-s).re ≠ 0 := by simp; linarith
  let g : S → ℝ := fun 𝔭 => 2 * (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s.re)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (f := g)
  · intro ⟨𝔭, h𝔭⟩
    set a := (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)
    have hN : 2 ≤ Ideal.absNorm 𝔭.asIdeal :=
      NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
    have h_cpow_norm : ‖(↑(Ideal.absNorm 𝔭.asIdeal) : ℂ) ^ (-s)‖ =
      (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ hre, Complex.neg_re]
    have h_cpow_le : (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) ≤ 1 / 2 := by
      calc (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re)
        ≤ (2 : ℝ) ^ (-s.re) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hN) (by linarith)
        _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
        _ = 1 / 2 := by norm_num
    have ha_norm : ‖a‖ ≤ 1 / 2 := by rw [h_cpow_norm]; exact h_cpow_le
    show ‖(1 - (Ideal.absNorm (⟨𝔭, h𝔭⟩ : S).1.asIdeal : ℂ) ^ (-s))⁻¹ - 1‖ ≤ g ⟨𝔭, h𝔭⟩
    show ‖(1 - a)⁻¹ - 1‖ ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s.re)
    calc ‖(1 - a)⁻¹ - 1‖
      ≤ 2 * ‖a‖ := norm_inv_one_sub_sub_one ha_norm
      _ = 2 * (↑(Ideal.absNorm 𝔭.asIdeal) : ℝ) ^ (-s.re) := by rw [h_cpow_norm]
  · show Summable g
    exact ((summable_primeIdeal_absNorm_rpow' K s.re hs).subtype S).mul_left 2

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_log_norm_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_log_norm_eq_tsum
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {s : ℝ}
-- given
  (hs : 1 < s) :
-- imply
  Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ = ∑' (𝔭 : S), -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) ∧ Summable (fun (𝔭 : S) => -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) ∧ Summable (fun (𝔭 : S) => (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) := by
-- proof
  set N : S → ℕ := fun 𝔭 => Ideal.absNorm (𝔭 : Prime' K).asIdeal with hN_def
  have hN_ge : ∀ 𝔭 : S, 2 ≤ N 𝔭 := fun 𝔭 =>
    NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
  have h_sum_rpow : Summable (fun 𝔭 : S => (N 𝔭 : ℝ) ^ (-s)) :=
    (summable_primeIdeal_absNorm_rpow' K s hs).subtype S
  have hN_pos : ∀ 𝔭 : S, (0 : ℝ) < (N 𝔭 : ℝ) := fun 𝔭 => by
    have := hN_ge 𝔭; exact_mod_cast (show 0 < N 𝔭 by omega)
  have h_rpow_pos : ∀ 𝔭 : S, 0 < (N 𝔭 : ℝ) ^ (-s) := fun 𝔭 => by
    exact Real.rpow_pos_of_pos (hN_pos 𝔭) (-s)
  have h_rpow_le_half : ∀ 𝔭 : S, (N 𝔭 : ℝ) ^ (-s) ≤ 1 / 2 := fun 𝔭 => by
    calc (N 𝔭 : ℝ) ^ (-s)
      ≤ (2 : ℝ) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hN_ge 𝔭) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      _ = 1 / 2 := by norm_num
  have h_rpow_lt_one : ∀ 𝔭 : S, (N 𝔭 : ℝ) ^ (-s) < 1 := fun 𝔭 =>
    lt_of_le_of_lt (h_rpow_le_half 𝔭) (by norm_num)
  have h_one_sub_pos : ∀ 𝔭 : S, 0 < 1 - (N 𝔭 : ℝ) ^ (-s) := fun 𝔭 => by linarith [h_rpow_lt_one 𝔭]
  have h_inv_pos : ∀ 𝔭 : S, 0 < (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := fun 𝔭 =>
    inv_pos.mpr (h_one_sub_pos 𝔭)
  have h_cpow_eq : ∀ 𝔭 : S, (N 𝔭 : ℂ) ^ (-(↑s : ℂ)) = ↑((N 𝔭 : ℝ) ^ (-s)) := fun 𝔭 => by
    rw [show (-(↑s : ℂ)) = (((-s) : ℝ) : ℂ) from by push_cast; ring]
    rw [show (N 𝔭 : ℂ) = ((N 𝔭 : ℝ) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg (N 𝔭)) (-s)).symm
  have h_factor_eq : ∀ 𝔭 : S,
    (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹ = ↑((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) := fun 𝔭 => by
    rw [h_cpow_eq]
    push_cast
    ring
  have h_norm_factor : ∀ 𝔭 : S,
    ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ = (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := fun 𝔭 => by
    rw [h_factor_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h_inv_pos 𝔭)]
  have h_sum_neg : Summable (fun 𝔭 : S => -(N 𝔭 : ℝ) ^ (-s)) := h_sum_rpow.neg
  have h_sum_log : Summable (fun 𝔭 : S => Real.log (1 + -(N 𝔭 : ℝ) ^ (-s))) :=
    Real.summable_log_one_add_of_summable h_sum_neg
  have h_sum_log' : Summable (fun 𝔭 : S => Real.log (1 - (N 𝔭 : ℝ) ^ (-s))) :=
    h_sum_log.congr (fun 𝔭 => by ring_nf)
  have h_sum_neg_log : Summable (fun 𝔭 : S =>
    -Real.log (1 - (N 𝔭 : ℝ) ^ (-s))) := h_sum_log'.neg
  have h_sum_log_inv : Summable (fun 𝔭 : S =>
    Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹)) := by
    refine h_sum_neg_log.congr (fun 𝔭 => ?_)
    rw [Real.log_inv]
  have h_mult : Multipliable (fun 𝔭 : S =>
    (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹) := by
    have hre : (1 : ℝ) < ((↑s : ℂ)).re := by simp [hs]
    exact partialDedekindZeta_multipliable S (↑s) hre
  have h_norm_tprod : ‖∏' 𝔭 : S, (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ =
    ∏' 𝔭 : S, ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ := h_mult.norm_tprod
  have h_tprod_norm_eq : ∏' 𝔭 : S, ‖(1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ =
    ∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ := tprod_congr (fun 𝔭 => h_norm_factor 𝔭)
  have h_exp_eq : Real.exp (∑' 𝔭 : S, Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹)) =
    ∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹ :=
    Real.rexp_tsum_eq_tprod h_inv_pos h_sum_log_inv
  have h_log_tprod : Real.log (∏' 𝔭 : S, (1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) =
    ∑' 𝔭 : S, Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) := by
    rw [← h_exp_eq, Real.log_exp]
  have h_log_inv_eq : ∀ 𝔭 : S,
    Real.log ((1 - (N 𝔭 : ℝ) ^ (-s))⁻¹) = -Real.log (1 - (N 𝔭 : ℝ) ^ (-s)) := fun 𝔭 =>
    Real.log_inv (1 - (N 𝔭 : ℝ) ^ (-s))
  have h_main : Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ =
    ∑' 𝔭 : S, -Real.log (1 - (N 𝔭 : ℝ) ^ (-s)) := by
    show Real.log ‖∏' 𝔭 : S, (1 - (N 𝔭 : ℂ) ^ (-(↑s : ℂ)))⁻¹‖ = _
    rw [h_norm_tprod, h_tprod_norm_eq, h_log_tprod]
    exact tsum_congr h_log_inv_eq
  exact ⟨h_main, h_sum_neg_log, h_sum_rpow⟩

end RayClassField

namespace RayClassField

/--
[card_primes_le_card_ideals_rl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma card_primes_le_card_ideals_rl
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {n : ℕ} :
-- imply
  Nat.card {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
-- proof
  Nat.card_le_card_of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

end RayClassField

namespace RayClassField

/--
[ideal_count_rpow_summable_rl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma ideal_count_rpow_summable_rl
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ (-σ))) := by
-- proof
  have hLS : LSeriesSummable
    (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _ (fun n => Nat.cast_nonneg _) zero_le_one
    · simp; exact hσ
    apply Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (𝕜 := ℝ)
      (a := NumberField.dedekindZeta_residue K)
    simp only [Real.rpow_one]
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]; congr 1; norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  exact (hLS.norm).of_nonneg_of_le (fun n => by positivity) (fun n => by
    rw [LSeries.norm_term_eq]; split_ifs with h
    · subst h
      simp [Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < σ)))]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg n)])

end RayClassField

namespace RayClassField

/--
[summable_primeIdeal_absNorm_rpow_rl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma summable_primeIdeal_absNorm_rpow_rl
  [Field K]
  [NumberField K]
  {K : Type*}
  [Field K]
  [NumberField K]
  {σ : ℝ}
-- given
  (hσ : 1 < σ) :
-- imply
  Summable (fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-σ)) := by
-- proof
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : Prime' K =>
    Ideal.absNorm 𝔭.asIdeal)).summable_iff]
  suffices h : Summable (fun p : (n : ℕ) × {𝔭 : Prime' K //
    Ideal.absNorm 𝔭.asIdeal = n} => ((p.1 : ℝ) ^ (-σ))) by
    exact h.congr (fun ⟨n, 𝔭, h⟩ => by
      simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
      congr 1; exact_mod_cast h.symm)
  rw [summable_sigma_of_nonneg (fun ⟨n, _⟩ => by positivity)]
  exact ⟨fun n => Summable.of_finite, by
    simp_rw [tsum_const, nsmul_eq_mul]
    exact Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_primes_le_card_ideals_rl K n) (by positivity))
      (ideal_count_rpow_summable_rl K σ hσ)⟩

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_eulerProductLog_remainder_limit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_eulerProductLog_remainder_limit
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)} :
-- imply
  ∃ C : ℝ, Filter.Tendsto (fun s : ℝ => ∑' (𝔭 : S), (-Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by
-- proof
  set f : S → ℝ → ℝ := fun 𝔭 s =>
    -Real.log (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) -
    (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s) with hf_def
  set u : S → ℝ := fun 𝔭 => 2 * (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ ((-2 : ℝ))
    with hu_def
  have hN : ∀ 𝔭 : S, (2 : ℝ) ≤ (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) := by
    intro ⟨𝔭, _⟩
    have h1 := 𝔭.ne_bot
    have h2 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by rwa [ne_eq, Ideal.absNorm_eq_zero_iff]
    have h3 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := by
      intro h; exact 𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    exact_mod_cast (show 1 < Ideal.absNorm 𝔭.asIdeal by omega)
  have h_cont_each : ∀ 𝔭 : S, ContinuousOn (f 𝔭) (Set.Ici 1) := by
    intro 𝔭
    have hN𝔭 := hN 𝔭
    have hN_pos : (0 : ℝ) < (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) := by positivity
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.log
      · apply ContinuousOn.sub continuousOn_const
        exact (continuous_const.rpow continuous_neg
          (fun _ => Or.inl hN_pos.ne')).continuousOn
      · intro s hs
        simp only [Set.mem_Ici] at hs
        have : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
          rw [Real.rpow_neg hN_pos.le, one_div]
          gcongr
          calc (2 : ℝ) ≤ _ := hN𝔭
            _ = _ ^ (1 : ℝ) := by simp
            _ ≤ _ ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
        linarith
    · exact (continuous_const.rpow continuous_neg
      (fun _ => Or.inl hN_pos.ne')).continuousOn
  have h_summable : Summable u := by
    have h_all := summable_primeIdeal_absNorm_rpow_rl K 2 (by norm_num : (1 : ℝ) < 2)
    have h_sub := h_all.subtype S
    exact (h_sub.const_smul 2).congr fun 𝔭 => by simp [u, Function.comp]
  have h_bound : ∀ 𝔭 : S, ∀ s ∈ Set.Ici (1 : ℝ), ‖f 𝔭 s‖ ≤ u 𝔭 := by
    intro 𝔭 s hs
    simp only [Set.mem_Ici] at hs
    have hN𝔭 := hN 𝔭
    set N := (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) with hN_def
    show ‖f 𝔭 s‖ ≤ u 𝔭
    simp only [hf_def, hu_def]
    rw [Real.norm_eq_abs]
    have hN0 : (0 : ℝ) ≤ N := by linarith
    have hx0 : 0 ≤ N ^ (-s) := by positivity
    have hx_half : N ^ (-s) ≤ 1 / 2 := by
      rw [Real.rpow_neg hN0, one_div]
      gcongr
      calc (2 : ℝ) ≤ N := hN𝔭
        _ = N ^ (1 : ℝ) := by simp
        _ ≤ N ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    have hx1 : N ^ (-s) < 1 := by linarith
    have hab : |N ^ (-s)| < 1 := by rwa [abs_of_nonneg hx0]
    have h1 := Real.abs_log_sub_add_sum_range_le hab 1
    simp only [Finset.range_one, Finset.sum_singleton, abs_of_nonneg hx0] at h1
    rw [show -(Real.log (1 - N ^ (-s))) - N ^ (-s) =
      -(N ^ (-s) + Real.log (1 - N ^ (-s))) from by ring, abs_neg]
    calc |N ^ (-s) + Real.log (1 - N ^ (-s))|
      ≤ (N ^ (-s)) ^ (1 + 1) / (1 - N ^ (-s)) := by
        convert h1 using 2
        simp [pow_succ, pow_zero]
      _ ≤ 2 * (N ^ (-s)) ^ 2 := by
        rw [show (1 : ℕ) + 1 = 2 from rfl]
        rw [div_le_iff₀ (by linarith)]; nlinarith
      _ = 2 * N ^ (-2 * s) := by
        rw [← Real.rpow_natCast (N ^ (-s)) 2, ← Real.rpow_mul hN0]; ring_nf
      _ ≤ 2 * N ^ ((-2 : ℝ)) := by
        gcongr
        · linarith
        · nlinarith
  have h_cont := continuousOn_tsum h_cont_each h_summable h_bound
  have h1_mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.self_mem_Ici
  exact ⟨_, (h_cont.continuousWithinAt h1_mem).tendsto.mono_left
    (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)⟩

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_eulerProductLog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_eulerProductLog
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)} :
-- imply
  ∃ C : ℝ, Filter.Tendsto (fun s : ℝ => Real.log ‖partialDedekindZeta K S ((s : ℂ))‖ - ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by
-- proof
  obtain ⟨C, hC⟩ := partialDedekindZeta_eulerProductLog_remainder_limit S
  refine ⟨C, ?_⟩
  refine hC.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  obtain ⟨h_eq, h_summable, h_summable_norm⟩ := partialDedekindZeta_log_norm_eq_tsum S hs
  rw [h_eq, h_summable.tsum_sub h_summable_norm]

end RayClassField

namespace RayClassField

/--
[eulerProduct_log_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma eulerProduct_log_asymptotic
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {n : ℕ+}
  {m : ℤ}
-- given
  (hm : HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m) :
-- imply
  ∃ C : ℝ, Filter.Tendsto (fun s : ℝ => (n : ℝ) * (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) - (m : ℝ) * Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds C) := by
-- proof
  obtain ⟨C₁, hC₁⟩ := meromorphic_poleOrder_realLog_limit _ m hm
  obtain ⟨C₂, hC₂⟩ := partialDedekindZeta_eulerProductLog S
  set D : ℝ → ℝ := fun s =>
    ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))
  set g : ℝ → ℝ := fun s => Real.log ‖partialDedekindZeta K S ((s : ℂ))‖
  have hC₁' : Filter.Tendsto (fun s : ℝ =>
    (n : ℝ) * g s + (m : ℝ) * Real.log (s - 1))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds C₁) := by
    refine hC₁.congr (fun s => ?_)
    simp only [g, Pi.pow_apply, norm_pow, Real.log_pow]
  have hC₂' : Filter.Tendsto (fun s : ℝ =>
    (n : ℝ) * (g s - D s))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds ((n : ℝ) * C₂)) :=
    hC₂.const_mul _
  have hMain : Filter.Tendsto (fun s : ℝ =>
    (n : ℝ) * D s + (m : ℝ) * Real.log (s - 1))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (C₁ - (n : ℝ) * C₂)) := by
    have := hC₁'.sub hC₂'
    refine this.congr (fun s => ?_)
    ring
  refine ⟨C₁ - (n : ℝ) * C₂, hMain.congr (fun s => ?_)⟩
  simp only [one_div, Real.log_inv]
  ring

end RayClassField

namespace RayClassField

/--
[poleOrder_implies_dirichletDensity_limit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma poleOrder_implies_dirichletDensity_limit
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {n : ℕ+}
  {m : ℤ}
-- given
  (hm : HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m) :
-- imply
  Filter.Tendsto (fun s : ℝ => (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) / Real.log (1 / (s - 1))) (nhdsWithin 1 (Set.Ioi 1)) (nhds ((m : ℝ) / (n : ℝ))) := by
-- proof
  obtain ⟨C, hC⟩ := eulerProduct_log_asymptotic hm
  set D : ℝ → ℝ := fun s =>
    ∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))
  set L : ℝ → ℝ := fun s => Real.log (1 / (s - 1))
  have hL : Filter.Tendsto L (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop := by
    have h_sub : Filter.Tendsto (fun s : ℝ => s - 1)
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
      apply Filter.Tendsto.inf
      · have : Filter.Tendsto (fun s : ℝ => s - 1) (nhds 1) (nhds (1 - 1)) :=
        (continuous_id.sub continuous_const).continuousAt
        simpa using this
      · rw [Filter.tendsto_principal_principal]
        intro s hs; simp only [Set.mem_Ioi] at hs ⊢; linarith
    have h_neg_log : Filter.Tendsto (fun s : ℝ => -Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h_sub)
    exact h_neg_log.congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs
      show -Real.log (s - 1) = L s
      simp only [L, one_div, Real.log_inv])
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos
  have h_ratio_zero : Filter.Tendsto
    (fun s => (↑n * D s - ↑m * L s) / (↑n * L s))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    hC.div_atTop (hL.const_mul_atTop hn)
  have h_eq : (fun s => (m : ℝ) / (n : ℝ) + (↑n * D s - ↑m * L s) / (↑n * L s))
    =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun s => D s / L s) := by
    filter_upwards [hL.eventually (Filter.eventually_ge_atTop 1)] with s hgs
    have hgs' : L s ≠ 0 := by linarith
    have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp
    ring
  rw [show ((m : ℝ) / (n : ℝ)) = (m : ℝ) / (n : ℝ) + 0 from by ring]
  exact (Filter.Tendsto.add tendsto_const_nhds h_ratio_zero).congr' h_eq

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_poleOrder_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_poleOrder_nonneg
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {n : ℕ+}
  {m : ℤ}
-- given
  (h : HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m) :
-- imply
  0 ≤ m := by
-- proof
  have hlim := poleOrder_implies_dirichletDensity_limit h
  have h_nonneg : (0 : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (1:ℝ) < 2 by norm_num))] with s hs1 hs2
    have h1 : 1 < s := hs1
    have h2 : s < 2 := hs2
    apply div_nonneg
    · exact tsum_nonneg fun 𝔭 => Real.rpow_nonneg (Nat.cast_nonneg _) _
    · apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith : (0:ℝ) < s - 1)]
      linarith
  have hn : (0 : ℝ) < (n : ℝ) := by positivity
  rw [le_div_iff₀ hn, zero_mul] at h_nonneg
  exact_mod_cast h_nonneg

end RayClassField

namespace RayClassField

/--
[polar_implies_dirichlet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma polar_implies_dirichlet
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ : ℚ}
-- given
  (h : HasPolarDensity K S ρ) :
-- imply
  HasDirichletDensity K S ρ := by
-- proof
  obtain ⟨n, m, hm, hρ⟩ := h
  have hlim := poleOrder_implies_dirichletDensity_limit hm
  have hcast : (ρ : ℝ) = (m : ℝ) / (n : ℝ) := by rw [hρ]; push_cast; ring
  unfold HasDirichletDensity
  rwa [hcast]

end RayClassField

namespace RayClassField

/--
[hasPolarDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma hasPolarDensity_nonneg
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ : ℚ}
-- given
  (h : HasPolarDensity K S ρ) :
-- imply
  0 ≤ ρ := by
-- proof
  obtain ⟨n, m, hm, hρ⟩ := h
  rw [hρ]
  apply div_nonneg
  · exact_mod_cast partialDedekindZeta_poleOrder_nonneg hm
  · exact_mod_cast n.pos.le

end RayClassField

namespace RayClassField

/--
[dirichletDensity_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma dirichletDensity_eq_some_iff
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ : ℚ} :
-- imply
  DirichletDensity K S = some ρ ↔ HasDirichletDensity K S ρ := by
-- proof
  classical
  constructor
  · intro h
    unfold DirichletDensity at h
    split_ifs at h with hex
    exact (Option.some_injective _ h) ▸ hex.choose_spec
  · intro h
    unfold DirichletDensity
    rw [dif_pos ⟨ρ, h⟩]
    congr 1
    exact hasDirichletDensity_unique (Exists.choose_spec ⟨ρ, h⟩) h

end RayClassField

namespace RayClassField

/--
[naturalDensity_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma naturalDensity_eq_some_iff
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {ρ : ℚ} :
-- imply
  NaturalDensity K S = some ρ ↔ HasNaturalDensity K S ρ := by
-- proof
  classical
  constructor
  · intro h
    unfold NaturalDensity at h
    split_ifs at h with hex
    exact (Option.some_injective _ h) ▸ hex.choose_spec
  · intro h
    unfold NaturalDensity
    rw [dif_pos ⟨ρ, h⟩]
    congr 1
    exact hasNaturalDensity_unique (Exists.choose_spec ⟨ρ, h⟩) h

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_dirichletSeries_summable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_dirichletSeries_summable
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
  {s : ℝ}
-- given
  (hs : 1 < s) :
-- imply
  Summable (fun (𝔭 : S) => ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) :=
-- proof
  (summable_primeIdeal_absNorm_rpow' K s hs).subtype S

end RayClassField

namespace RayClassField

/--
[HasMeromorphicContinuationWithPoleOrder_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma HasMeromorphicContinuationWithPoleOrder_mul
  [Field K]
  [NumberField K]
  {f g : ℂ → ℂ}
  {m₁ m₂ : ℤ}
-- given
  (hf : HasMeromorphicContinuationWithPoleOrder f m₁)
  (hg : HasMeromorphicContinuationWithPoleOrder g m₂) :
-- imply
  HasMeromorphicContinuationWithPoleOrder (f * g) (m₁ + m₂) := by
-- proof
  refine ⟨hf.1.mul hg.1, ?_⟩
  rw [meromorphicOrderAt_mul hf.1 hg.1, hf.2, hg.2]
  simp only [← WithTop.coe_add, Int.neg_add]

end RayClassField

namespace RayClassField

/--
[HasMeromorphicContinuationWithPoleOrder_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma HasMeromorphicContinuationWithPoleOrder_pow
  [Field K]
  [NumberField K]
  {f : ℂ → ℂ}
  {m : ℤ}
  {n : ℕ}
-- given
  (hf : HasMeromorphicContinuationWithPoleOrder f m) :
-- imply
  HasMeromorphicContinuationWithPoleOrder (f ^ n) (m * n) := by
-- proof
  refine ⟨hf.1.pow n, ?_⟩
  rw [meromorphicOrderAt_pow hf.1, hf.2]
  have : (↑n : WithTop ℤ) * ↑(-m) = ↑(↑n * (-m) : ℤ) := by exact_mod_cast rfl
  rw [this]; congr 1; ring

end RayClassField

namespace RayClassField

/--
[partialDedekindZeta_finite_meromorphicOrderAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma partialDedekindZeta_finite_meromorphicOrderAt_zero
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {S : Set (Prime' K)}
-- given
  (hS : S.Finite) :
-- imply
  meromorphicOrderAt (partialDedekindZeta K S) 1 = 0 := by
-- proof
  haveI : Fintype ↥S := hS.fintype
  let F : ↥S → ℂ → ℂ := fun 𝔭 s =>
    (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹
  have heq : partialDedekindZeta K S = fun s => ∏ 𝔭 : ↥S, F 𝔭 s := by
    ext s; exact tprod_fintype _
  rw [heq]
  have hne_cast : ∀ (𝔭 : ↥S), (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ≠ 0 := by
    intro 𝔭
    have : Ideal.absNorm (𝔭 : Prime' K).asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
      omega
    exact Nat.cast_ne_zero.mpr this
  have hfactor_analytic : ∀ (𝔭 : ↥S), AnalyticAt ℂ (F 𝔭) 1 := by
    intro 𝔭
    have hne := hne_cast 𝔭
    show AnalyticAt ℂ (fun s => (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹) 1
    apply AnalyticAt.inv
    · apply AnalyticAt.sub analyticAt_const
      have hrw : ∀ s : ℂ, (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s) =
        Complex.exp (-s * Complex.log (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ)) := by
        intro s; rw [Complex.cpow_def_of_ne_zero hne]; ring_nf
      simp_rw [hrw]
      exact ((analyticAt_id (𝕜 := ℂ)).neg.mul analyticAt_const).cexp
    · have hN_gt : 1 < Ideal.absNorm (𝔭 : Prime' K).asIdeal :=
      NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
      rw [show (-(1 : ℂ)) = (-1 : ℤ) by push_cast; ring, Complex.cpow_intCast]
      simp only [zpow_neg_one]
      rw [sub_ne_zero]
      intro h
      have h2 : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) = 1 := by
        rw [eq_comm, inv_eq_one] at h; exact h
      have : Ideal.absNorm (𝔭 : Prime' K).asIdeal = 1 := by exact_mod_cast h2
      omega
  have hprod_analytic : AnalyticAt ℂ (fun s => ∏ 𝔭 : ↥S, F 𝔭 s) 1 :=
    Finset.analyticAt_fun_prod Finset.univ (fun 𝔭 _ => hfactor_analytic 𝔭)
  have hprod_ne : (fun s => ∏ 𝔭 : ↥S, F 𝔭 s) (1 : ℂ) ≠ 0 := by
    simp only
    apply Finset.prod_ne_zero_iff.mpr
    intro 𝔭 _
    simp only [F]
    apply inv_ne_zero
    have hN_gt : 1 < Ideal.absNorm (𝔭 : Prime' K).asIdeal :=
      NumberField.HeightOneSpectrum.one_lt_absNorm (𝔭 : Prime' K)
    rw [show (-(1 : ℂ)) = (-1 : ℤ) by push_cast; ring, Complex.cpow_intCast]
    simp only [zpow_neg_one]
    rw [sub_ne_zero]
    intro h
    have h2 : (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) = 1 := by
      rw [eq_comm, inv_eq_one] at h; exact h
    have : Ideal.absNorm (𝔭 : Prime' K).asIdeal = 1 := by exact_mod_cast h2
    omega
  rw [hprod_analytic.meromorphicOrderAt_eq,
    hprod_analytic.analyticOrderAt_eq_zero.mpr hprod_ne]
  simp

end RayClassField

namespace RayClassField

/--
[adjoin_range_eq_fieldRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma adjoin_range_eq_fieldRange
  [Field K]
  [NumberField K]
  [Field K']
  [Field L']
  [Field E']
  [Algebra K' L']
  [Algebra K' E']
  {f : L' →ₐ[K'] E'} :
-- imply
  IntermediateField.adjoin K' (Set.range f) = f.fieldRange :=
-- proof
  le_antisymm (IntermediateField.adjoin_le_iff.mpr fun _ ⟨y, hy⟩ => ⟨y, hy⟩)
    (fun _ ⟨y, hy⟩ => IntermediateField.subset_adjoin K' _ ⟨y, hy⟩)

end RayClassField

namespace RayClassField

/--
[inclusion_fieldRange_sup_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma inclusion_fieldRange_sup_eq_top
  [Field K]
  [NumberField K]
  [Field K']
  [Field A']
  [Algebra K' A']
  {E' F' : IntermediateField K' A'} :
-- imply
  (IntermediateField.inclusion (le_sup_left : E' ≤ E' ⊔ F')).fieldRange ⊔ (IntermediateField.inclusion (le_sup_right : F' ≤ E' ⊔ F')).fieldRange = ⊤ :=
-- proof
  IntermediateField.map_injective (E' ⊔ F').val (by
    rw [IntermediateField.map_sup, AlgHom.map_fieldRange, AlgHom.map_fieldRange,
      show (E' ⊔ F').val.comp (IntermediateField.inclusion le_sup_left) = E'.val from by ext; rfl,
      show (E' ⊔ F').val.comp (IntermediateField.inclusion le_sup_right) = F'.val from by ext; rfl,
      IntermediateField.fieldRange_val, IntermediateField.fieldRange_val,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val])

end RayClassField

namespace RayClassField

/--
[comp_equiv_fieldRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma comp_equiv_fieldRange
  [Field K]
  [NumberField K]
  [Field K']
  [Field L']
  [Field E']
  [Field F']
  [Algebra K' L']
  [Algebra K' E']
  [Algebra K' F']
  {f : E' →ₐ[K'] F'}
  {g : L' ≃ₐ[K'] E'} :
-- imply
  (f.comp g.toAlgHom).fieldRange = f.fieldRange := by
-- proof
  ext x; simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  exact ⟨fun ⟨y, h⟩ => ⟨g y, h⟩, fun ⟨y, h⟩ => ⟨g.symm y, by simp [h]⟩⟩

end RayClassField

namespace RayClassField

/--
[split_iff_in_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma split_iff_in_kernel
  [Field K]
  [NumberField K]
  {K L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [KroneckerWeber.IsAbelianExtension K L]
  {𝔪 : Modulus K}
  {𝔭 : Prime' K}
-- given
  (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  SplitsCompletely K L 𝔭 ↔ ArtinMap K L 𝔪 (primeCoprime K 𝔪 𝔭 h_coprime) = 1 := by
-- proof
  unfold SplitsCompletely
  rw [artinMap_at_prime_eq_frobenius]

end RayClassField

namespace RayClassField

/--
[modulus_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
lemma modulus_support_finite
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  Set.Finite {𝔭 : Prime' K | 𝔪 (Place.finite 𝔭) ≠ 0} := by
-- proof
  have : {𝔭 : Prime' K | 𝔪 (Place.finite 𝔭) ≠ 0} =
    Place.finite ⁻¹' {v | 𝔪 v ≠ 0} := by ext; simp
  rw [this]
  exact 𝔪.finite_support.preimage (fun a _ b _ hab => by cases hab; rfl)

end RayClassField

/--
[hasTrivialValuation_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma hasTrivialValuation_one_eq
  [Field K]
  [NumberField K]
  {v : FinitePlace K} :
-- imply
  HasTrivialValuation (1 : (FracIdeal K)ˣ) v := by
-- proof
  apply RayClassField.hasTrivialValuation_one v

/--
[hasTrivialValuation_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma hasTrivialValuation_mul_eq
  [Field K]
  [NumberField K]
  {a b : (FracIdeal K)ˣ}
  {v : FinitePlace K}
-- given
  (ha : HasTrivialValuation a v)
  (hb : HasTrivialValuation b v) :
-- imply
  HasTrivialValuation (a * b) v := by
-- proof
  apply RayClassField.hasTrivialValuation_mul ha hb

/--
[choosePrimeOver_over](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma choosePrimeOver_over_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔭 : FinitePlace K} :
-- imply
  (choosePrimeOver K L 𝔭).comap (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal := by
-- proof
  apply RayClassField.choosePrimeOver_over K L 𝔭

/--
[choosePrimeOver_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma choosePrimeOver_ne_bot_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔭 : FinitePlace K} :
-- imply
  choosePrimeOver K L 𝔭 ≠ ⊥ := by
-- proof
  apply RayClassField.choosePrimeOver_ne_bot K L 𝔭

/--
[primeAsUnitFracIdeal_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma primeAsUnitFracIdeal_coprime_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝔭 : FinitePlace K}
-- given
  (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  (primeAsUnitFracIdeal K 𝔭 : (FracIdeal K)ˣ) ∈ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  apply RayClassField.primeAsUnitFracIdeal_coprime K 𝔪 𝔭 h𝔭

/--
[count_spanSingleton_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma count_spanSingleton_eq_zero_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {v : FinitePlace K}
  {x : K}
-- given
  (hx : x ≠ 0)
  (hv : v.valuation K x = 1) :
-- imply
  FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x) = 0 := by
-- proof
  apply RayClassField.count_spanSingleton_eq_zero K v x hx hv

/--
[count_eq_zero_of_isCoprimeTo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma count_eq_zero_of_isCoprimeTo_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {I : (FracIdeal K)ˣ}
  {v : FinitePlace K}
-- given
  (h : FracIdeal.IsCoprimeTo I v) :
-- imply
  FractionalIdeal.count K v (I : FracIdeal K) = 0 := by
-- proof
  apply RayClassField.count_eq_zero_of_isCoprimeTo K I v h

/--
[primeCoprime_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma primeCoprime_val_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K}
  {𝔭 : FinitePlace K}
-- given
  (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
-- imply
  (primeCoprime K 𝔪 𝔭 h𝔭).val = primeAsUnitFracIdeal K 𝔭 := by
-- proof
  apply RayClassField.primeCoprime_val K 𝔪 𝔭 h𝔭

/--
[primeAsUnitFracIdeal_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma primeAsUnitFracIdeal_val_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔭 : FinitePlace K} :
-- imply
  (primeAsUnitFracIdeal K 𝔭 : FracIdeal K) = 𝔭.asIdeal := by
-- proof
  apply RayClassField.primeAsUnitFracIdeal_val K 𝔭

/--
[fracIdealsCoprime_closure_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma fracIdealsCoprime_closure_primes_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  Subgroup.closure (primesCoprime K 𝔪) = ⊤ := by
-- proof
  apply RayClassField.fracIdealsCoprime_closure_primes K 𝔪

/--
[primesCoprime_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma primesCoprime_eq_range_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  primesCoprime K 𝔪 = Set.range (fun (p : CoprimePrimes K 𝔪) => primeCoprime K 𝔪 p.1 p.2) := by
-- proof
  apply RayClassField.primesCoprime_eq_range K 𝔪

/--
[freeGroupToCoprime_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma freeGroupToCoprime_surjective_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  Function.Surjective (freeGroupToCoprime K 𝔪) := by
-- proof
  apply RayClassField.freeGroupToCoprime_surjective K 𝔪

/--
[fractionalIdeal_mulEquiv_finsupp_primeAsUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma fractionalIdeal_mulEquiv_finsupp_primeAsUnit_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {p : FinitePlace K} :
-- imply
  fractionalIdeal_mulEquiv_finsupp K (primeAsUnitFracIdeal K p) = Multiplicative.ofAdd (Finsupp.single p 1) := by
-- proof
  apply RayClassField.fractionalIdeal_mulEquiv_finsupp_primeAsUnit K p

/--
[freeGroupToCoprime_ker_le_commutator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma freeGroupToCoprime_ker_le_commutator_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 : Modulus K} :
-- imply
  (freeGroupToCoprime K 𝔪).ker ≤ commutator (FreeGroup (CoprimePrimes K 𝔪)) := by
-- proof
  apply RayClassField.freeGroupToCoprime_ker_le_commutator K 𝔪

/--
[artinMap_ker_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma artinMap_ker_condition_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [KroneckerWeber.IsAbelianExtension K L]
  {𝔪 : Modulus K} :
-- imply
  (freeGroupToCoprime K 𝔪).ker ≤ (freeGroupToGal K L 𝔪).ker := by
-- proof
  apply RayClassField.artinMap_ker_condition K L 𝔪

/--
[artinMapExists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma artinMapExists_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [KroneckerWeber.IsAbelianExtension K L]
  {𝔪 : Modulus K} :
-- imply
  ∃ (ψ : FracIdealsCoprime K 𝔪 →* (L ≃ₐ[K] L)), ∀ (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0), ψ (primeCoprime K 𝔪 𝔭 h𝔭) = FrobeniusAutomorphism K L 𝔭 := by
-- proof
  apply RayClassField.artinMapExists K L 𝔪

/--
[choosePrimeOver_comap_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma choosePrimeOver_comap_ne_bot_eq
  [Field K]
  [NumberField K]
  {K : Type u}
  {L : Type u}
  {M : Type u}
  [Field K]
  [Field L]
  [Field M]
  [NumberField K]
  [NumberField L]
  [NumberField M]
  [Algebra K L]
  [Algebra K M]
  [Algebra L M]
  [IsGalois K L]
  [IsGalois K M]
  [IsScalarTower K L M]
  {𝔭 : FinitePlace K} :
-- imply
  (choosePrimeOver K M 𝔭).comap (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)) ≠ ⊥ := by
-- proof
  apply RayClassField.choosePrimeOver_comap_ne_bot K L M 𝔭

/--
[embedding_im_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma embedding_im_zero_eq
  [Field K]
  [NumberField K]
  {w : NumberField.InfinitePlace K}
  {x : K}
-- given
  (hw : w.IsReal) :
-- imply
  (w.embedding x).im = 0 := by
-- proof
  apply RayClassField.embedding_im_zero hw x

/--
[Modulus.finitePartIdeal_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma finitePartIdeal_ne_bot_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  𝔪.finitePartIdeal ≠ ⊥ := by
-- proof
  apply RayClassField.Modulus.finitePartIdeal_ne_bot 𝔪

/--
[lemma_21_7_ideal_class_coprime_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma lemma_21_7_ideal_class_coprime_rep_eq
  [Field K]
  [NumberField K]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {𝔞 : Ideal A}
  {c : ClassGroup A}
-- given
  (h𝔞 : 𝔞 ≠ ⊥) :
-- imply
  ∃ (I : nonZeroDivisors (Ideal A)), ClassGroup.mk0 I = c ∧ (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum A, 𝔭.asIdeal ∣ 𝔞 → ¬(𝔭.asIdeal ∣ (I : Ideal A))) := by
-- proof
  apply RayClassField.lemma_21_7_ideal_class_coprime_rep A 𝔞 c h𝔞

/--
[valuation_algebraMap_unit_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma valuation_algebraMap_unit_eq_one_eq
  [Field K]
  [NumberField K]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
  {u : (NumberField.RingOfIntegers K)ˣ} :
-- imply
  v.valuation K (algebraMap (NumberField.RingOfIntegers K) K u.val) = 1 := by
-- proof
  apply RayClassField.valuation_algebraMap_unit_eq_one v u

/--
[okUnitsInUnitsCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma okUnitsInUnitsCoprime_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {u : (NumberField.RingOfIntegers K)ˣ} :
-- imply
  okUnitsToKUnits u ∈ UnitsCoprime_subgroup' K 𝔪 := by
-- proof
  apply RayClassField.okUnitsInUnitsCoprime 𝔪 u

/--
[toPrincipalIdeal_mem_FracIdealsCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma toPrincipalIdeal_mem_FracIdealsCoprime_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {α : Kˣ}
-- given
  (hα : α ∈ UnitsCoprime_subgroup' K 𝔪) :
-- imply
  toPrincipalIdeal (NumberField.RingOfIntegers K) K α ∈ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  apply RayClassField.toPrincipalIdeal_mem_FracIdealsCoprime 𝔪 α hα

/--
[principalIdealMap_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma principalIdealMap_val_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {α : UnitsCoprime_subgroup' K 𝔪} :
-- imply
  ((principalIdealMap 𝔪 α).val : (FracIdeal K)ˣ).val = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α : Kˣ) : K) := by
-- proof
  apply RayClassField.principalIdealMap_val 𝔪 α

/--
[principalIdealMap_congruent_to_ray](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma principalIdealMap_congruent_to_ray_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {α : UnitsCoprime_subgroup' K 𝔪}
-- given
  (hα : (α : Kˣ) ∈ UnitsCongruent_subgroup' K 𝔪) :
-- imply
  principalIdealMap 𝔪 α ∈ RayGroup K 𝔪 := by
-- proof
  apply RayClassField.principalIdealMap_congruent_to_ray 𝔪 α hα

/--
[valuation_eq_one_of_spanSingleton_coprime'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma valuation_eq_one_of_spanSingleton_coprime'_eq
  [Field K]
  [NumberField K]
  {v : FinitePlace K}
  {α : Kˣ}
-- given
  (h0 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α) v)
  (h1 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α)⁻¹ v) :
-- imply
  v.valuation K (α : K) = 1 := by
-- proof
  apply RayClassField.valuation_eq_one_of_spanSingleton_coprime' v α h0 h1

/--
[exactSeq_exact_at_ray_class](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma exactSeq_exact_at_ray_class_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  MonoidHom.range (exactSeq_map3 𝔪) = MonoidHom.ker (exactSeq_map4 𝔪) := by
-- proof
  apply RayClassField.exactSeq_exact_at_ray_class 𝔪

/--
[mk0_mem_FracIdealsCoprime_of_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma mk0_mem_FracIdealsCoprime_of_coprime_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))}
-- given
  (hI : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔭.asIdeal ∣ 𝔪.finitePartIdeal → ¬(𝔭.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K)))) :
-- imply
  FractionalIdeal.mk0 K I ∈ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  apply RayClassField.mk0_mem_FracIdealsCoprime_of_coprime 𝔪 I hI

/--
[classGroup_mk_comp_subtype_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma classGroup_mk_comp_subtype_surjective_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Function.Surjective (ClassGroup.mk.comp (FracIdealsCoprime_subgroup K 𝔪).subtype) := by
-- proof
  apply RayClassField.classGroup_mk_comp_subtype_surjective 𝔪

/--
[exactSeq_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma exactSeq_surjective_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Function.Surjective (exactSeq_map4 𝔪) := by
-- proof
  apply RayClassField.exactSeq_surjective 𝔪

/--
[Modulus.infSupportFinset_isReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma infSupportFinset_isReal_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {w : NumberField.InfinitePlace K}
-- given
  (hw : w ∈ 𝔪.infSupportFinset) :
-- imply
  w.IsReal := by
-- proof
  apply RayClassField.Modulus.infSupportFinset_isReal 𝔪 hw

/--
[embedding_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma embedding_re_ne_zero_eq
  [Field K]
  [NumberField K]
  {w : NumberField.InfinitePlace K}
  {a : Kˣ}
-- given
  (hw : w.IsReal) :
-- imply
  (w.embedding (a : K)).re ≠ 0 := by
-- proof
  apply RayClassField.embedding_re_ne_zero hw a

/--
[signAtPlace_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma signAtPlace_mul_eq
  [Field K]
  [NumberField K]
  {w : NumberField.InfinitePlace K}
  {a b : Kˣ}
-- given
  (hw : w.IsReal) :
-- imply
  signAtPlace hw (a * b) = signAtPlace hw a + signAtPlace hw b := by
-- proof
  apply RayClassField.signAtPlace_mul hw a b

/--
[signAtPlace_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma signAtPlace_eq_zero_iff_eq
  [Field K]
  [NumberField K]
  {w : NumberField.InfinitePlace K}
  {α : Kˣ}
-- given
  (hw : w.IsReal) :
-- imply
  signAtPlace hw α = 0 ↔ 0 < (w.embedding (α : K)).re := by
-- proof
  apply RayClassField.signAtPlace_eq_zero_iff hw α

/--
[coprime_rep_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma coprime_rep_exists_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {α : UnitsCoprime_subgroup' K 𝔪} :
-- imply
  ∃ (a b : NumberField.RingOfIntegers K), IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a) ∧ IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b) ∧ algebraMap (NumberField.RingOfIntegers K) K a / algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K) := by
-- proof
  apply RayClassField.coprime_rep_exists 𝔪 α

/--
[coprime_rep_well_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma coprime_rep_well_def_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {a b c d : NumberField.RingOfIntegers K}
-- given
  (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
  (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
  (hc : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal c))
  (hd : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal d))
  (hab : algebraMap (NumberField.RingOfIntegers K) K a / algebraMap (NumberField.RingOfIntegers K) K b = algebraMap (NumberField.RingOfIntegers K) K c / algebraMap (NumberField.RingOfIntegers K) K d) :
-- imply
  ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by
-- proof
  apply RayClassField.coprime_rep_well_def 𝔪 ha hb hc hd hab

/--
[finset_prod_ideal_le_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma finset_prod_ideal_le_factor_eq
  [Field K]
  [NumberField K]
  [CommRing R]
  [DecidableEq ι]
  {S : Finset ι}
  {f : ι → Ideal R}
  {j : ι}
-- given
  (hj : j ∈ S) :
-- imply
  S.prod f ≤ f j := by
-- proof
  apply RayClassField.finset_prod_ideal_le_factor S f j hj

/--
[unit_mod_ideal_not_in_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma unit_mod_ideal_not_in_prime_eq
  [Field K]
  [NumberField K]
  [CommRing R]
  {I 𝔭 : Ideal R}
  {b : R}
-- given
  (hI𝔭 : I ≤ 𝔭)
  (h𝔭 : 𝔭 ≠ ⊤)
  (hb : IsUnit (Ideal.Quotient.mk I b)) :
-- imply
  b ∉ 𝔭 := by
-- proof
  apply RayClassField.unit_mod_ideal_not_in_prime hI𝔭 h𝔭 hb

/--
[coprime_rep_unit_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma coprime_rep_unit_eq_one_iff_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {a b : NumberField.RingOfIntegers K}
-- given
  (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
  (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
  (hab : algebraMap (NumberField.RingOfIntegers K) K a / algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K)) :
-- imply
  ha.unit * hb.unit⁻¹ = 1 ↔ ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (((α : Kˣ) : K) - 1) ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
-- proof
  apply RayClassField.coprime_rep_unit_eq_one_iff 𝔪 ha hb hab

/--
[finitePartMapHom_ker_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma finitePartMapHom_ker_iff_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {α : UnitsCoprime_subgroup' K 𝔪} :
-- imply
  finitePartMapHom K 𝔪 α = 1 ↔ ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (((α : Kˣ) : K) - 1) ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
-- proof
  apply RayClassField.finitePartMapHom_ker_iff 𝔪 α

/--
[weak_approx_nonzero_with_val_and_sign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma weak_approx_nonzero_with_val_and_sign_eq
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  [DecidablePred pos]
-- given
  (pos : 𝔪.infSupportFinset → Prop) :
-- imply
  ∃ (x : K) (_ : x ≠ 0), (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K x = 1) ∧ (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset), (pos ⟨w, hw⟩ → 0 < (w.embedding x).re) ∧ (¬ pos ⟨w, hw⟩ → (w.embedding x).re < 0)) := by
-- proof
  apply RayClassField.weak_approx_nonzero_with_val_and_sign 𝔪 pos

/--
[weak_approx_sign_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma weak_approx_sign_coprime_eq
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {s : 𝔪.infSupportFinset → Multiplicative (ZMod 2)} :
-- imply
  ∃ (α : Kˣ), (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (α : K) = 1) ∧ (∀ (w : NumberField.InfinitePlace K) (hw : w ∈ 𝔪.infSupportFinset), Multiplicative.ofAdd (signAtPlace (𝔪.infSupportFinset_isReal hw) α) = s ⟨w, hw⟩) := by
-- proof
  apply RayClassField.weak_approx_sign_coprime 𝔪 s

/--
[signMapHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma signMapHom_surjective_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Function.Surjective (signMapHom K 𝔪) := by
-- proof
  apply RayClassField.signMapHom_surjective 𝔪

/--
[weak_approx_coprime_sign_finitePart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma weak_approx_coprime_sign_finitePart_eq
  [Field K]
  [NumberField K]
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ} :
-- imply
  ∃ (α : UnitsCoprime_subgroup' K 𝔪), signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
-- proof
  apply RayClassField.weak_approx_coprime_sign_finitePart 𝔪 u

/--
[finitePartMapHom_surj_on_ker_sign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma finitePartMapHom_surj_on_ker_sign_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _}
  {u : (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ} :
-- imply
  ∃ α : UnitsCoprime_subgroup' K 𝔪, signMapHom K 𝔪 α = 1 ∧ finitePartMapHom K 𝔪 α = u := by
-- proof
  apply RayClassField.finitePartMapHom_surj_on_ker_sign 𝔪 u

/--
[signTimesFinitePart_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma signTimesFinitePart_surjective_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Function.Surjective (MonoidHom.prod (signMapHom K 𝔪) (finitePartMapHom K 𝔪)) := by
-- proof
  apply RayClassField.signTimesFinitePart_surjective 𝔪

/--
[finite_part_map_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma finite_part_map_exists_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  ∃ (f : UnitsCoprime_subgroup' K 𝔪 →* (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ), (∀ α : UnitsCoprime_subgroup' K 𝔪, f α = 1 ↔ ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → v.valuation K (((α : Kˣ) : K) - 1) ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧ Function.Surjective (MonoidHom.prod (signMapHom K 𝔪) f) := by
-- proof
  apply RayClassField.finite_part_map_exists 𝔪

/--
[theorem_21_8_quotient_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
-/
@[path]
private lemma theorem_21_8_quotient_iso_eq
  [Field K]
  [NumberField K]
  {𝔪 : @Modulus K _ _} :
-- imply
  Nonempty (QuotientUnits K 𝔪 ≃* SignsTimesUnits K 𝔪) := by
-- proof
  apply RayClassField.theorem_21_8_quotient_iso 𝔪


-- created on 2026-10-23
