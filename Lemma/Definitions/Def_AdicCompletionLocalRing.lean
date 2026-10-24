import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]

section Kernel

variable (I : Ideal A)

theorem evalₐ_algebraMap (n : ℕ) (a : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk _ a := by
  rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

theorem mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

theorem exists_eq_algebraMap_add (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, ∃ y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)),
      x = algebraMap A (AdicCompletion I A) a + y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, x - algebraMap A _ a, ?_, by ring⟩
  rw [← ker_evalₐ_eq_map_pow I hI, RingHom.mem_ker, map_sub, evalₐ_algebraMap, ha, sub_self]

theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  haveI : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I A)).mpr (isAdicComplete hI)
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

theorem isUnit_add_of_mem_map (hI : I.FG) {u x : AdicCompletion I A} (hu : IsUnit u)
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (u + x) := by
  have e : u + x = u * (1 + ↑hu.unit⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [e]
  exact hu.mul (isUnit_one_add_of_mem_map I hI (Ideal.mul_mem_left _ _ hx))

end Kernel

section Local

variable [IsLocalRing A]

theorem isUnit_of_isUnit_algebraMap {a : A}
    (h : IsUnit (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) : IsUnit a := by
  by_contra ha
  have hmem : a ∈ maximalIdeal A ^ 1 := by
    rw [pow_one]; exact (mem_maximalIdeal a).mpr ha
  have h1 := h.map (evalₐ (maximalIdeal A) 1)
  rw [evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, isUnit_zero_iff] at h1
  exact (maximalIdeal.isMaximal A).ne_top
    ((pow_one (maximalIdeal A)).symm.trans (Ideal.Quotient.zero_eq_one_iff.mp h1))

theorem isUnit_one_add_of_mem_map_maximalIdeal (h𝔪 : (maximalIdeal A).FG)
    {x : AdicCompletion (maximalIdeal A) A}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_mem_map _ h𝔪 hx

variable [IsNoetherianRing A]

theorem maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _

instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg

theorem maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n = RingHom.ker (evalₐ (maximalIdeal A) n) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow _ maximalIdeal_fg]

theorem maximalIdeal_eq_ker_evalₐ_one :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) = RingHom.ker (evalₐ (maximalIdeal A) 1) := by
  rw [← maximalIdeal_pow_eq_ker_evalₐ, pow_one]

theorem mem_maximalIdeal_iff (x : AdicCompletion (maximalIdeal A) A) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ↔ evalₐ (maximalIdeal A) 1 x = 0 := by
  rw [maximalIdeal_eq_ker_evalₐ_one, RingHom.mem_ker]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

theorem quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

theorem quotientMaximalIdealPowAlgHom_bijective (n : ℕ) :
    Function.Bijective (quotientMaximalIdealPowAlgHom (A := A) k n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotientMaximalIdealPowAlgHom_mk, quotientMaximalIdealPowAlgHom_mk] at hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker, map_sub, hxy, sub_self]
  · intro z
    obtain ⟨x, rfl⟩ := surjective_evalₐ (maximalIdeal A) n z
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective k n)

theorem quotientMaximalIdealPowAlgEquiv_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

theorem quotientMaximalIdealPowAlgEquiv_mk_algebraMap (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ (algebraMap A _ a))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquiv_mk, evalₐ_algebraMap]

end Scalars

end Local

section Transport

variable [IsLocalRing A] [IsNoetherianRing A]
variable {k : Type*} [CommRing k] [Algebra k A] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]
variable (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

omit [IsNoetherianRing A] [IsLocalRing B] in
theorem isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) : IsUnit (Φ x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩

theorem comap_maximalIdeal_algEquiv :
    (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B)
      = maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  ext x
  show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]

theorem map_maximalIdeal_algEquiv :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
        (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
  rw [← comap_maximalIdeal_algEquiv Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

theorem maximalIdeal_eq_map_algEquiv :
    maximalIdeal B = (maximalIdeal A).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← Ideal.map_map, ← maximalIdeal_eq_map, map_maximalIdeal_algEquiv]

theorem maximalIdeal_pow_eq_map_algEquiv (n : ℕ) :
    maximalIdeal B ^ n = (maximalIdeal A ^ n).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [Ideal.map_pow, ← maximalIdeal_eq_map_algEquiv]

theorem algEquiv_algebraMap_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    Φ (algebraMap A _ a) ∈ maximalIdeal B := by
  rw [maximalIdeal_eq_map_algEquiv Φ]
  exact Ideal.mem_map_of_mem _ ha

noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

theorem quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n (Ideal.Quotient.mk _ (Φ (algebraMap A _ a)))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquivOfAlgEquiv, AlgEquiv.trans_apply,
    ← Ideal.quotientEquivAlg_mk (I := maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      (J := maximalIdeal B ^ n) (f := Φ) (hIJ := by rw [Ideal.map_pow, map_maximalIdeal_algEquiv]),
    AlgEquiv.symm_apply_apply, quotientMaximalIdealPowAlgEquiv_mk_algebraMap]

end Transport

end AdicCompletion

#print axioms AdicCompletion.ker_evalₐ_eq_map_pow
#print axioms AdicCompletion.isUnit_one_add_of_mem_map
#print axioms AdicCompletion.instIsLocalRingMaximalIdeal
#print axioms AdicCompletion.maximalIdeal_eq_map
#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquiv
#print axioms AdicCompletion.maximalIdeal_eq_map_algEquiv
#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquivOfAlgEquiv
