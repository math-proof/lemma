import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import Instance.AdicCompletionLocalRing

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]

section Local

variable [IsLocalRing A]
variable [IsNoetherianRing A]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  have mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
      x ∈ RingHom.ker (evalₐ (maximalIdeal A) n) ↔
        x ∈ LinearMap.ker (eval (maximalIdeal A) A n) := by
    have h : ((maximalIdeal A) ^ n • ⊤ : Ideal A) = (maximalIdeal A) ^ n := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [RingHom.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hx; rw [← factor_evalₐ_eq_eval (maximalIdeal A) x h.ge, hx]; exact RingHom.map_zero _
    · intro hx; rw [← factor_eval_eq_evalₐ (maximalIdeal A) x h.le, hx]; exact LinearMap.map_zero _
  have ker_evalₐ_eq_map_pow (hI : (maximalIdeal A).FG) (n : ℕ) :
      RingHom.ker (evalₐ (maximalIdeal A) n) =
        ((maximalIdeal A) ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
    ext x
    rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem]
  have maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n =
        RingHom.ker (evalₐ (maximalIdeal A) n) := by
    rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow maximalIdeal_fg]
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  have mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
      x ∈ RingHom.ker (evalₐ (maximalIdeal A) n) ↔
        x ∈ LinearMap.ker (eval (maximalIdeal A) A n) := by
    have h : ((maximalIdeal A) ^ n • ⊤ : Ideal A) = (maximalIdeal A) ^ n := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [RingHom.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hx; rw [← factor_evalₐ_eq_eval (maximalIdeal A) x h.ge, hx]; exact RingHom.map_zero _
    · intro hx; rw [← factor_eval_eq_evalₐ (maximalIdeal A) x h.le, hx]; exact LinearMap.map_zero _
  have ker_evalₐ_eq_map_pow (hI : (maximalIdeal A).FG) (n : ℕ) :
      RingHom.ker (evalₐ (maximalIdeal A) n) =
        ((maximalIdeal A) ^ n).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
    ext x
    rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem]
  have maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n =
        RingHom.ker (evalₐ (maximalIdeal A) n) := by
    rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow maximalIdeal_fg]
  have quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
      quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
    rfl
  have quotientMaximalIdealPowAlgHom_bijective (n : ℕ) :
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
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective n)

end Scalars

end Local

section Transport

variable [IsLocalRing A] [IsNoetherianRing A]
variable {k : Type*} [CommRing k] [Algebra k A] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]
variable (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  have isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) :
      IsUnit (Φ x) ↔ IsUnit x :=
    ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩
  have comap_maximalIdeal_algEquiv :
      (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B) =
        maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
    ext x
    show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
    rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]
  have map_maximalIdeal_algEquiv :
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
          (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
    rw [← comap_maximalIdeal_algEquiv]
    exact Ideal.map_comap_of_surjective _ Φ.surjective _
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

end Transport

end AdicCompletion
