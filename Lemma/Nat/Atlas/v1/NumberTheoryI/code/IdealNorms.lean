import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.IdealNorms
open nonZeroDivisors DirectSum Ideal Polynomial UniqueFactorizationMonoid DedekindKummer DedekindKummer.NF
open NumberField
open Ideal Polynomial UniqueFactorizationMonoid
open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField


/--
[localModuleIndex_comp_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma localModuleIndex_comp_equiv
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup M]
  [Module R M]
  {φ : M →ₗ[R] M}
  {u v : M ≃ₗ[R] M} :
-- imply
  localModuleIndex (K := K) ((u : M →ₗ[R] M) ∘ₗ φ ∘ₗ (v : M →ₗ[R] M)) = localModuleIndex (K := K) φ := by
-- proof
  simp only [localModuleIndex, LinearMap.det_comp, map_mul]
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨(LinearEquiv.det u)⁻¹ * (LinearEquiv.det v)⁻¹, ?_⟩
  simp only [Units.smul_def, Units.val_mul, Algebra.smul_def, ← LinearEquiv.coe_det, ← map_mul]
  congr 1
  have hu := Units.inv_mul (LinearEquiv.det u)
  have hv := Units.inv_mul (LinearEquiv.det v)
  calc ↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det v)⁻¹ *
    (↑(LinearEquiv.det u) * (LinearMap.det φ * ↑(LinearEquiv.det v)))
    = (↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det u)) *
      (↑(LinearEquiv.det v)⁻¹ * ↑(LinearEquiv.det v)) * LinearMap.det φ := by ring
    _ = 1 * 1 * LinearMap.det φ := by rw [hu, hv]
    _ = LinearMap.det φ := by ring

/--
[localModuleIndex_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma localModuleIndex_comp
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup M]
  [Module R M]
  {φ ψ : M →ₗ[R] M} :
-- imply
  localModuleIndex (K := K) (φ ∘ₗ ψ) = localModuleIndex (K := K) φ * localModuleIndex (K := K) ψ := by
-- proof
  simp only [localModuleIndex, LinearMap.det_comp, map_mul,
    FractionalIdeal.spanSingleton_mul_spanSingleton]

/--
[localModuleIndex_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma localModuleIndex_id
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup M]
  [Module R M] :
-- imply
  localModuleIndex (K := K) (LinearMap.id : M →ₗ[R] M) = 1 := by
-- proof
  simp [localModuleIndex, LinearMap.det_id, map_one, FractionalIdeal.spanSingleton_one]
section GlobalModuleIndex

/--
[prod_ne_zero_of_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma prod_ne_zero_of_ne_bot
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {n : ℕ}
  {J : Fin n → Ideal A}
-- given
  (hJ : ∀ i, J i ≠ ⊥) :
-- imply
  (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
-- proof
  rw [FractionalIdeal.coeIdeal_ne_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Ne, Ideal.mul_eq_bot]
    push Not
    exact ⟨ih (J ∘ Fin.castSucc) (fun i => hJ (Fin.castSucc i)), hJ (Fin.last n)⟩
end GlobalModuleIndex
section CyclicQuotient
end CyclicQuotient
section ConcreteModuleIndex
variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/--
[concreteModuleIndex_eq_cardQuot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_eq_cardQuot
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  concreteModuleIndex N = Submodule.cardQuot N :=
-- proof
  (Submodule.cardQuot_apply N).symm

/--
[concreteModuleIndex_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_top
  [Ring R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  concreteModuleIndex (⊤ : Submodule R M) = 1 := by
-- proof
  rw [concreteModuleIndex_eq_cardQuot, Submodule.cardQuot_top]

/--
[concreteModuleIndex_mul_tower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_mul_tower
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {N P : Submodule R M}
-- given
  (hPN : P ≤ N) :
-- imply
  Nat.card ↥(N.map P.mkQ) * Nat.card (M ⧸ N) = Nat.card (M ⧸ P) :=
-- proof
  Submodule.card_quotient_mul_card_quotient N P hPN

/--
[concreteModuleIndex_ideal_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_ideal_mul
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [CommRing S]
  [IsDedekindDomain S]
  [Module.Free ℤ S]
  {I J : Ideal S} :
-- imply
  Nat.card (S ⧸ (I * J : Ideal S)) = Nat.card (S ⧸ I) * Nat.card (S ⧸ J) := by
-- proof
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
  exact cardQuot_mul I J
end ConcreteModuleIndex
section DetFormula
variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/--
[concreteModuleIndex_eq_natAbs_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_eq_natAbs_det
  [AddCommGroup M]
  [Module.Free ℤ M]
  [Module.Finite ℤ M]
  [Fintype ι]
  [DecidableEq ι]
  {b : Basis ι ℤ M}
  {N : Submodule ℤ M}
  {bN : Basis ι ℤ N} :
-- imply
  (b.det ((↑) ∘ bN)).natAbs = concreteModuleIndex N :=
-- proof
  Submodule.natAbs_det_basis_change b N bN

/--
[concreteModuleIndex_eq_natAbs_det_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma concreteModuleIndex_eq_natAbs_det_equiv
  [AddCommGroup M]
  [Module.Free ℤ M]
  [Module.Finite ℤ M]
  {N : Submodule ℤ M}
  [EquivLike E M N]
  [AddEquivClass E M N]
  {e : E} :
-- imply
  Int.natAbs (LinearMap.det (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) = concreteModuleIndex N :=
-- proof
  Submodule.natAbs_det_equiv N e
end DetFormula
section NormConcreteIndex
open NumberField

/--
[idealNorm_eq_concreteModuleIndex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_eq_concreteModuleIndex
  [Field K]
  [NumberField K]
  {I : Ideal (𝓞 K)} :
-- imply
  Ideal.absNorm I = concreteModuleIndex (I : Submodule (𝓞 K) (𝓞 K)) := by
-- proof
  rw [concreteModuleIndex, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/--
[absNorm_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma absNorm_mul_eq
  [Field K]
  [NumberField K]
  {I J : Ideal (𝓞 K)} :
-- imply
  Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
-- proof
  map_mul (Ideal.absNorm) I J
end NormConcreteIndex
open Ideal Polynomial UniqueFactorizationMonoid
namespace DedekindKummer
variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
variable {x : S} {I : Ideal R}
attribute [local instance] Ideal.Quotient.field

namespace DedekindKummer

/--
[dedekind_kummer_multiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma dedekind_kummer_multiplicity
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsDomain R]
  [IsIntegrallyClosed R]
  [IsDedekindDomain S]
  [Module.IsTorsionFree R S]
  {x : S}
  {I : Ideal R}
  {J : Ideal S}
-- given
  (hI : I.IsMaximal)
  (hI' : I ≠ ⊥)
  (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  (hx' : IsIntegral R x)
  (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
-- imply
  emultiplicity J (I.map (algebraMap R S)) = emultiplicity (↑(dedekind_kummer_bijection hI hI' hx hx' ⟨J, hJ⟩)) (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) :=
-- proof
  KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ
open Classical in
set_option backward.isDefEq.respectTransparency false in

end DedekindKummer

namespace DedekindKummer

/--
[dedekind_kummer_prime_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma dedekind_kummer_prime_formula
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsDomain R]
  [IsIntegrallyClosed R]
  [IsDedekindDomain S]
  [Module.IsTorsionFree R S]
  {x : S}
  {I : Ideal R}
  {Q : R[X]}
-- given
  (hI : I.IsMaximal)
  (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
  (hI' : I ≠ ⊥)
  (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  (hx' : IsIntegral R x) :
-- imply
  ((dedekind_kummer_bijection hI hI' hx hx').symm ⟨_, hQ⟩).val = Ideal.span (↑(I.map (algebraMap R S)) ∪ {Polynomial.aeval x Q}) :=
-- proof
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    hI hQ hI' hx hx'
open Classical in
set_option backward.isDefEq.respectTransparency false in

end DedekindKummer

namespace DedekindKummer

/--
[dedekind_kummer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma dedekind_kummer
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [IsDomain R]
  [IsIntegrallyClosed R]
  [IsDedekindDomain S]
  [Module.IsTorsionFree R S]
  {x : S}
  {I : Ideal R}
-- given
  (hI : I.IsMaximal)
  (hI' : I ≠ ⊥)
  (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
  (hx' : IsIntegral R x) :
-- imply
  normalizedFactors (I.map (algebraMap R S)) = Multiset.map (fun f => ((dedekind_kummer_bijection hI hI' hx hx').symm f : Ideal S)) (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach :=
-- proof
  KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx'
end DedekindKummer
section IdealNorm

end DedekindKummer

/--
[idealNorm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_apply
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal B} :
-- imply
  idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
-- proof
  Ideal.relNorm_apply A I

/--
[idealNorm_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_ne_zero
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal B}
-- given
  (hI : I ≠ 0) :
-- imply
  idealNorm A I ≠ 0 := by
-- proof
  simp only [idealNorm, ne_eq]
  rw [show (0 : Ideal A) = ⊥ from rfl, Ideal.relNorm_eq_bot_iff,
    show (⊥ : Ideal B) = 0 from rfl]
  exact hI

/--
[idealNorm_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_eq_zero_iff
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal B} :
-- imply
  idealNorm A I = 0 ↔ I = 0 := by
-- proof
  simp only [idealNorm, show (0 : Ideal A) = ⊥ from rfl, show (0 : Ideal B) = ⊥ from rfl,
    Ideal.relNorm_eq_bot_iff]

/--
[idealNorm_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_mono
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I J : Ideal B}
-- given
  (h : I ≤ J) :
-- imply
  idealNorm A I ≤ idealNorm A J :=
-- proof
  Ideal.relNorm_mono A h

/--
[idealNorm_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_principal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {α : B} :
-- imply
  idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.intNorm A B α} :=
-- proof
  Ideal.relNorm_singleton A α

/--
[idealNorm_principal_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_principal_free
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Free A B]
  {α : B} :
-- imply
  idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.norm A α} := by
-- proof
  rw [idealNorm_principal, Algebra.intNorm_eq_norm]

/--
[idealNorm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_mul
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I J : Ideal B} :
-- imply
  idealNorm A (I * J) = idealNorm A I * idealNorm A J :=
-- proof
  map_mul (idealNorm A) I J

/--
[idealNorm_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_one
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B] :
-- imply
  idealNorm A (1 : Ideal B) = 1 :=
-- proof
  map_one (idealNorm A)

/--
[relNorm_ne_bot_of_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma relNorm_ne_bot_of_ne_bot
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [IsIntegrallyClosed A]
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [IsIntegrallyClosed B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal B}
-- given
  (_ : I ≠ ⊥) :
-- imply
  Ideal.relNorm A I ≠ ⊥ := by
-- proof
  rwa [ne_eq, Ideal.relNorm_eq_bot_iff]
section IdealNorm
variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/--
[idealNorm_eq_span_norms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_eq_span_norms
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal B} :
-- imply
  idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
-- proof
  Ideal.relNorm_apply A I

/--
[idealNorm_eq_span_fieldNorms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_eq_span_fieldNorms
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [Module.Free A B]
  {I : Ideal B} :
-- imply
  idealNorm A I = Ideal.span (Algebra.norm A '' (I : Set B)) := by
-- proof
  rw [idealNorm_eq_span_norms]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩
end IdealNorm
section IdealNormPrime
variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/--
[idealNorm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_prime
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  [PerfectField (FractionRing A)]
  {Q : Ideal B}
  {p : Ideal A}
  [Q.LiesOver p]
  [Q.IsMaximal]
  [p.IsMaximal] :
-- imply
  idealNorm A Q = p ^ p.inertiaDeg Q :=
-- proof
  Ideal.relNorm_eq_pow_of_isMaximal Q p
attribute [local instance] FractionRing.liftAlgebra in

/--
[idealNorm_map_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma idealNorm_map_eq_pow
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B]
  {I : Ideal A} :
-- imply
  idealNorm A (I.map (algebraMap A B)) = I ^ Module.finrank (FractionRing A) (FractionRing B) :=
-- proof
  Ideal.relNorm_algebraMap B I
end IdealNormPrime
section NormNumberField
open NumberField

/--
[absNorm_eq_card_quot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma absNorm_eq_card_quot
  [Field K]
  [NumberField K]
  {I : Ideal (𝓞 K)} :
-- imply
  Ideal.absNorm I = Nat.card ((𝓞 K) ⧸ I) := by
-- proof
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/--
[absNorm_mul_card_quotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma absNorm_mul_card_quotient_eq
  [Field K]
  [NumberField K]
  {I J : Ideal (𝓞 K)}
-- given
  (hle : J ≤ I) :
-- imply
  Ideal.absNorm I * Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K))) (I : Submodule (𝓞 K) (𝓞 K))) = Ideal.absNorm J := by
-- proof
  rw [mul_comm, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Submodule.card_quotient_mul_card_quotient _ _ hle

/--
[moduleIndex_eq_absNorm_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma moduleIndex_eq_absNorm_quotient
  [Field K]
  [NumberField K]
  {I J : Ideal (𝓞 K)}
  {C : Ideal (𝓞 K)}
-- given
  (hI : I ≠ ⊥)
  (hle : J ≤ I)
  (hC : J = I * C) :
-- imply
  Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K))) (I : Submodule (𝓞 K) (𝓞 K))) = Ideal.absNorm C := by
-- proof
  have tower := absNorm_mul_card_quotient_eq I J hle
  have mul_norm : Ideal.absNorm J = Ideal.absNorm I * Ideal.absNorm C := by
    rw [hC, map_mul]
  have hI_pos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  exact Nat.eq_of_mul_eq_mul_left hI_pos (tower.trans mul_norm)
end NormNumberField
namespace DedekindKummer.NF
open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField
variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

namespace DedekindKummer.NF

/--
[inertiaDeg_eq_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma inertiaDeg_eq_natDegree
  [Field K]
  [NumberField K]
  {θ : 𝓞 K}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {Q : (ZMod p)[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  inertiaDeg (span {(p : ℤ)}) ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) = Q.natDegree :=
-- proof
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

end DedekindKummer.NF

namespace DedekindKummer.NF

/--
[ramificationIdx_eq_multiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
lemma ramificationIdx_eq_multiplicity
  [Field K]
  [NumberField K]
  {θ : 𝓞 K}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {Q : (ZMod p)[X]}
-- given
  (hp : ¬ p ∣ RingOfIntegers.exponent θ)
  (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
-- imply
  (span {(p : ℤ)}).ramificationIdx ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) = multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
-- proof
  NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

end DedekindKummer.NF

/--
[idealNorm_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
private lemma idealNorm_def_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B] :
-- imply
  (idealNorm A : Ideal B →*₀ Ideal A) = Ideal.relNorm A := by
-- proof
  apply idealNorm_def A

/--
[idealNorm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean)
-/
@[path]
private lemma idealNorm_zero_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsIntegrallyClosed A]
  [IsDedekindDomain A]
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.IsTorsionFree A B] :
-- imply
  idealNorm A (0 : Ideal B) = 0 := by
-- proof
  apply idealNorm_zero A


-- created on 2026-10-23
