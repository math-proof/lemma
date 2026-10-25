import Lemma.AlgebraicCurve.SemistableCharts
import Lemma.ModularCurve.FullLevelJacobian
import Lemma.ModularCurve.QAdicPlace
import Lemma.ModularCurve.JZeroSemistableSpecialization
import Lemma.AlgebraicCurve.SemistableChartsComap
import Structure.ModularCurve_FullLevelSemistableCovering

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable


set_option synthInstance.maxHeartbeats 400000 in


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
