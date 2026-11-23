module

public import Def.HeckeGalois_EichlerShimura
public import Instance.ModularCurve_SpecializationWitness
public import Structure.ModularCurve_SpecializationWitness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Family

variable (J' : Type*) [AddCommGroup J']


variable {J'}

namespace CommutingHeckeFamily

variable (fam : CommutingHeckeFamily J')

noncomputable def endHom : HeckeAlg →+* Module.End ℤ J' :=
  ((Algebra.adjoin ℤ (Set.range fam.T)).val).toRingHom.comp
    (MvPolynomial.aeval
      (fun q : Nat.Primes =>
        (⟨fam.T q, Algebra.subset_adjoin (Set.mem_range_self q)⟩ :
          Algebra.adjoin ℤ (Set.range fam.T))) :
      HeckeAlg →ₐ[ℤ] Algebra.adjoin ℤ (Set.range fam.T)).toRingHom

@[reducible] noncomputable def module : Module HeckeAlg J' :=
  Module.compHom _ fam.endHom

end CommutingHeckeFamily

end Family

section Packaging

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]


end Packaging

end ModularCurve

end

end
