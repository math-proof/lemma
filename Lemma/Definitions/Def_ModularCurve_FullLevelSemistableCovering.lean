import Lemma.Definitions.Def_AlgebraicCurve_SemistableCharts
import Lemma.Definitions.Def_ModularCurve_FullLevelJacobian
import Lemma.Definitions.Def_ModularCurve_QAdicPlace
import Lemma.Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Lemma.Definitions.Def_AlgebraicCurve_SemistableChartsComap

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

def lineInfty : CuspidalType.ProjLine q :=
  Projectivization.mk (ZMod q) ![1, 0] (by
    intro h
    have h0 := congr_fun h 0
    simp at h0)

set_option synthInstance.maxHeartbeats 400000 in

structure SemistableCovering
    (SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) : Type 1 where

  FIg : CuspidalType.ProjLine q → Type
  [instFieldIg : ∀ ℓ, Field (FIg ℓ)]
  [instAlgebraIg : ∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]

  FSS : ↥SS → Type
  [instFieldSS : ∀ s, Field (FSS s)]
  [instAlgebraSS : ∀ s, Algebra (ResidueField A) (FSS s)]

  CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ)

  CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s)

  An : CuspidalType.ProjLine q → ↥SS → Annulus A (fieldBar q M')

  An' : CuspidalType.ProjLine q → ↥SS → Annulus A (fieldBar q M')

  xs : ∀ ℓ : CuspidalType.ProjLine q, ↥SS → Place (ResidueField A) (FIg ℓ)

  xt : CuspidalType.ProjLine q → ∀ s : ↥SS, Place (ResidueField A) (FSS s)

  dom_eq : ∀ ℓ s, (An' ℓ s).dom = (An ℓ s).dom

  modulus_eq : ∀ ℓ s, (An' ℓ s).modulus = (An ℓ s).modulus

  modulus_ne_zero : ∀ ℓ s, ((An ℓ s).modulus : AlgebraicClosure ℚ) ≠ 0

  param_mul : ∀ ℓ s, (An' ℓ s).param * (An ℓ s).param =
    algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((An ℓ s).modulus : AlgebraicClosure ℚ)

  isAttached : ∀ ℓ s, (An ℓ s).IsAttached (CIg ℓ) (xs ℓ s) ∧ (An' ℓ s).IsAttached (CSS s) (xt ℓ s)

  existsUnique_xs_eq : ∀ ℓ, ∀ x ∈ (CIg ℓ).nodes, ∃! s, xs ℓ s = x

  existsUnique_xt_eq : ∀ s, ∀ x ∈ (CSS s).nodes, ∃! ℓ, xt ℓ s = x

  partition : ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
    (∃ ℓ, P ∈ (CIg ℓ).dom ∧ (∀ ℓ', P ∈ (CIg ℓ').dom → ℓ' = ℓ) ∧ (∀ s, P ∉ (CSS s).dom) ∧ ∀ ℓ' s, P ∉ (An ℓ' s).dom) ∨
    (∃ s, P ∈ (CSS s).dom ∧ (∀ s', P ∈ (CSS s').dom → s' = s) ∧ (∀ ℓ, P ∉ (CIg ℓ).dom) ∧ ∀ ℓ s', P ∉ (An ℓ s').dom) ∨
    (∃ ℓ s, P ∈ (An ℓ s).dom ∧ (∀ ℓ' s', P ∈ (An ℓ' s').dom → ℓ' = ℓ ∧ s' = s) ∧
      (∀ ℓ', P ∉ (CIg ℓ').dom) ∧ ∀ s', P ∉ (CSS s').dom)

  cusp_mem : ∃ P ∈ (CIg (lineInfty q)).dom,
    P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')

  hasPrincipalDivisors_Ig : ∀ ℓ, HasPrincipalDivisors (ResidueField A) (FIg ℓ)
  hasPrincipalDivisors_SS : ∀ s, HasPrincipalDivisors (ResidueField A) (FSS s)

  isRational_Ig : ∀ ℓ (x : Place (ResidueField A) (FIg ℓ)), x.IsRational
  isRational_SS : ∀ s (x : Place (ResidueField A) (FSS s)), x.IsRational

attribute [instance] SemistableCovering.instFieldIg SemistableCovering.instAlgebraIg
  SemistableCovering.instFieldSS SemistableCovering.instAlgebraSS

example {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A SS) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) :=
  𝒞.partition P

example {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A SS) (ℓ : CuspidalType.ProjLine q) (s : ↥SS) :
    (𝒞.An ℓ s).IsAttached (𝒞.CIg ℓ) (𝒞.xs ℓ s) :=
  (𝒞.isAttached ℓ s).1

namespace SemistableCovering

variable {q M' A}
variable {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

def EquivClauses (𝒞 : SemistableCovering q M' A SS) : Prop :=
  ∀ (ζ : Idx q) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
      (∀ ℓ, ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CIg (σ ℓ)).integers ∧
        ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CIg (σ ℓ)).dom) ∧
      (∀ s, ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CSS s).integers ∧
        ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CSS s).dom) ∧
      (∀ ℓ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.An (σ ℓ) s).dom ∧
        (𝒞.An ℓ s).modulus = (𝒞.An (σ ℓ) s).modulus)

theorem equivClauses_iff (𝒞 : SemistableCovering q M' A SS) :
    𝒞.EquivClauses ↔
      ∀ (ζ : Idx q) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
          (∀ ℓ, ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CIg (σ ℓ)).integers ∧
            ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CIg (σ ℓ)).dom) ∧
          (∀ s, ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).integers = (𝒞.CSS s).integers ∧
            ((𝒞.CSS s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.CSS s).dom) ∧
          (∀ ℓ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ γ)).dom = (𝒞.An (σ ℓ) s).dom ∧
            (𝒞.An ℓ s).modulus = (𝒞.An (σ ℓ) s).modulus) :=
  Iff.rfl

end SemistableCovering

end ModularCurve.FullLevel

end
