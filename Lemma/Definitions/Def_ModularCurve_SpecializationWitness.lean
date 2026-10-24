import Lemma.Definitions.Def_HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Family

variable (J' : Type*) [AddCommGroup J']

structure CommutingHeckeFamily : Type _ where

  T : Nat.Primes → Module.End ℤ J'

  comm : ∀ q q' : Nat.Primes, Commute (T q) (T q')

variable {J'}

namespace CommutingHeckeFamily

variable (fam : CommutingHeckeFamily J')

theorem isMulCommutative_adjoin :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range fam.T)) := by
  refine Algebra.isMulCommutative_adjoin ℤ ?_
  rintro x ⟨q, rfl⟩ y ⟨q', rfl⟩
  exact fam.comm q q'

instance commRing_adjoin : CommRing ↥(Algebra.adjoin ℤ (Set.range fam.T)) where
  __ := (inferInstance : Ring ↥(Algebra.adjoin ℤ (Set.range fam.T)))
  mul_comm a b := fam.isMulCommutative_adjoin.is_comm.comm a b

noncomputable def endHom : HeckeAlg →+* Module.End ℤ J' :=
  ((Algebra.adjoin ℤ (Set.range fam.T)).val).toRingHom.comp
    (MvPolynomial.aeval
      (fun q : Nat.Primes =>
        (⟨fam.T q, Algebra.subset_adjoin (Set.mem_range_self q)⟩ :
          Algebra.adjoin ℤ (Set.range fam.T))) :
      HeckeAlg →ₐ[ℤ] Algebra.adjoin ℤ (Set.range fam.T)).toRingHom

theorem endHom_heckeGen (q : Nat.Primes) : fam.endHom (heckeGen q) = fam.T q := by
  show ((Algebra.adjoin ℤ (Set.range fam.T)).val)
      ((MvPolynomial.aeval
        (fun q : Nat.Primes =>
          (⟨fam.T q, Algebra.subset_adjoin (Set.mem_range_self q)⟩ :
            Algebra.adjoin ℤ (Set.range fam.T))))
        (MvPolynomial.X q)) = fam.T q
  rw [MvPolynomial.aeval_X]
  rfl

@[reducible] noncomputable def module : Module HeckeAlg J' :=
  Module.compHom _ fam.endHom

theorem module_heckeGen_smul (q : Nat.Primes) (y : J') :
    letI := fam.module
    heckeGen q • y = fam.T q y := by
  letI := fam.module
  show fam.endHom (heckeGen q) y = fam.T q y
  rw [fam.endHom_heckeGen]

end CommutingHeckeFamily

end Family

section Packaging

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

structure SpecializationWitnessData (A : ValuationSubring L) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Type _ where

  J' : Type

  [addCommGroup : AddCommGroup J']

  fam : CommutingHeckeFamily J'

  sp : J →+ J'

  F : J' →+ J'

  hecke_comm_gen : ∀ (q : Nat.Primes) (x : J), sp (heckeGen q • x) = fam.T q (sp x)

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ → ∀ x : J, sp (σ • x) = F (sp x)

  injective_torsion : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  relation : ∀ y : J', F (F y) - fam.T ⟨ℓ, hℓ⟩ (F y) + ℓ • y = 0

attribute [instance] SpecializationWitnessData.addCommGroup

end Packaging

end ModularCurve
