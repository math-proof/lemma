module
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Data.Fintype.Units
public import Instance.NarrowRayClassGroup
open NumberField nonZeroDivisors IsDedekindDomain


public section

noncomputable section

namespace Deep.NTSupply


section Carriers

variable (K : Type*) [Field K] [NumberField K]

def coprimeToModulus (𝔣 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
    FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = 0}
  mul_mem' := by
    intro I J hI hJ v hv
    have h : ((I * J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
        (I : FractionalIdeal ((𝓞 K)⁰) K) * (J : FractionalIdeal ((𝓞 K)⁰) K) := Units.val_mul I J
    rw [h, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  one_mem' := by
    intro v _
    rw [Units.val_one, FractionalIdeal.count_one]
  inv_mem' := by
    intro I hI v hv
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

def narrowRaySet (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
    (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) ∧
    (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)}

def narrowRaySubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  Subgroup.closure (narrowRaySet K 𝔣)

abbrev NarrowRayClassGroup (𝔣 : Ideal (𝓞 K)) : Type _ :=
  ↥(coprimeToModulus K 𝔣) ⧸ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)

def NarrowRayClassGroup.mk (𝔣 : Ideal (𝓞 K)) :
    ↥(coprimeToModulus K 𝔣) →* NarrowRayClassGroup K 𝔣 :=
  QuotientGroup.mk' _

end Carriers

section Symbol

variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]

def raySymbol (f : HeightOneSpectrum (𝓞 K) → M) (I : FractionalIdeal ((𝓞 K)⁰) K) : M :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v ^ FractionalIdeal.count K v I

def raySymbolUnitsHom (f : HeightOneSpectrum (𝓞 K) → M) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ →* M where
  toFun I := raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K)
  map_one' := by simp [raySymbol, FractionalIdeal.count_one]
  map_mul' I J := by
    simp only [Units.val_mul]
    exact raySymbol_mul K f I.ne_zero J.ne_zero

def raySymbolHom (𝔣 : Ideal (𝓞 K)) (f : HeightOneSpectrum (𝓞 K) → M) :
    ↥(coprimeToModulus K 𝔣) →* M :=
  (raySymbolUnitsHom K f).comp (coprimeToModulus K 𝔣).subtype

end Symbol

section Finiteness

variable (K : Type*) [Field K] [NumberField K]

def raySet (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
    (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)}

def rayClasses (𝔣 : Ideal (𝓞 K)) : Set (NarrowRayClassGroup K 𝔣) :=
  (NarrowRayClassGroup.mk K 𝔣) ''
    {y : ↥(coprimeToModulus K 𝔣) | (y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ raySet K 𝔣}

def rayClassSubgroup (𝔣 : Ideal (𝓞 K)) : Subgroup (NarrowRayClassGroup K 𝔣) :=
  Subgroup.closure (rayClasses K 𝔣)

def principalUnit (a : 𝓞 K) (ha : a ≠ 0) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  FractionalIdeal.mk0 K ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha)⟩

def toClassGroup (𝔣 : Ideal (𝓞 K)) : ↥(coprimeToModulus K 𝔣) →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk (R := 𝓞 K) (K := K)).comp (coprimeToModulus K 𝔣).subtype

def narrowRayClassGroupToClassGroup (𝔣 : Ideal (𝓞 K)) :
    NarrowRayClassGroup K 𝔣 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (toClassGroup K 𝔣) (narrowRaySubgroupOf_le_ker K 𝔣)

def rayClassGroupToClassGroup (𝔣 : Ideal (𝓞 K)) :
    NarrowRayClassGroup K 𝔣 ⧸ rayClassSubgroup K 𝔣 →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (rayClassSubgroup K 𝔣) (narrowRayClassGroupToClassGroup K 𝔣)
    (rayClassSubgroup_le_ker K 𝔣)

def MovingLemma (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ x₀ : K, x₀ ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) x₀) = 0) →
    ∃ β : 𝓞 K, β ≠ 0 ∧ β - 1 ∈ 𝔣 ∧
      ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K β * x₀

end Finiteness

section Packaging

variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]

def primeUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero (by
    rw [Ne, Submodule.zero_eq_bot]
    exact v.ne_bot)⟩

def primeClass (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    NarrowRayClassGroup K 𝔣 :=
  NarrowRayClassGroup.mk K 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩

def raySymbolDescend {𝔣 : Ideal (𝓞 K)} (f : HeightOneSpectrum (𝓞 K) → M)
    (hkill : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K f ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1) :
    NarrowRayClassGroup K 𝔣 →* M :=
  QuotientGroup.lift ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (raySymbolHom K 𝔣 f) (narrowRaySubgroupOf_le_ker_raySymbolHom K f hkill)

def raySymbolIdealHom (f : HeightOneSpectrum (𝓞 K) → M) : ↥(Ideal (𝓞 K))⁰ →* M :=
  (raySymbolUnitsHom K f).comp (FractionalIdeal.mk0 K)

end Packaging


#print axioms Deep.NTSupply.coprimeToModulus
#print axioms Deep.NTSupply.mem_coprimeToModulus_iff
#print axioms Deep.NTSupply.narrowRaySet
#print axioms Deep.NTSupply.narrowRaySubgroup
#print axioms Deep.NTSupply.narrowRaySubgroup_le_coprimeToModulus
#print axioms Deep.NTSupply.NarrowRayClassGroup
#print axioms Deep.NTSupply.NarrowRayClassGroup.mk
#print axioms Deep.NTSupply.one_mem_narrowRaySet
#print axioms Deep.NTSupply.raySymbol
#print axioms Deep.NTSupply.raySymbol_mul
#print axioms Deep.NTSupply.raySymbolHom
#print axioms Deep.NTSupply.raySymbolHom_prime
#print axioms Deep.NTSupply.raySymbolDescend
#print axioms Deep.NTSupply.raySymbolDescend_mk
#print axioms Deep.NTSupply.raySymbolDescend_primeClass
#print axioms Deep.NTSupply.raySymbolIdealHom
#print axioms Deep.NTSupply.primeUnit
#print axioms Deep.NTSupply.primeClass
#print axioms Deep.NTSupply.movingLemma
#print axioms Deep.NTSupply.finite
#print axioms Deep.NTSupply.coprimeToModulus_top
#print axioms Deep.NTSupply.finite_closure_of_involutions

end Deep.NTSupply

end
