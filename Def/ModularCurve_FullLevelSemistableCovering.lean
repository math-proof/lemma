module
public import Def.AlgebraicCurve_SemistableCharts
public import Def.ModularCurve_FullLevelJacobian
public import Def.ModularCurve_QAdicPlace
public import Theorem.Scheme.JZeroSemistableSpecialization
public import Def.AlgebraicCurve_SemistableChartsComap
public import Structure.ModularCurve_FullLevelSemistableCovering
set_option autoImplicit false


public section

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing ValuationSubring AlgEquiv

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable


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

end SemistableCovering

end ModularCurve.FullLevel

end
