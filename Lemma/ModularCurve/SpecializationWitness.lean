import Def.HeckeGalois_EichlerShimura
import Instance.ModularCurve_SpecializationWitness
import Structure.ModularCurve_SpecializationWitness

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Family

variable (J' : Type*) [AddCommGroup J']


variable {J'}

namespace CommutingHeckeFamily

variable (fam : CommutingHeckeFamily J')

theorem isMulCommutative_adjoin :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range fam.T)) := by
  refine Algebra.isMulCommutative_adjoin ℤ ?_
  rintro x ⟨q, rfl⟩ y ⟨q', rfl⟩
  exact fam.comm q q'

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


end Packaging

end ModularCurve
