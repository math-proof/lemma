import Def.ModularCurve_FullLevelSemistableCoveringW2

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing DrinfeldCurve CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def NaturalityClauses (𝒞 : SemistableCovering q M' A W) : Prop :=

  (∀ τ ∈ A.inertiaSubgroupIn ℚ,
    let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
    ∀ s, (∀ f : fieldBar q M', f ∈ (𝒞.CSS s).integers ↔ g • f ∈ (𝒞.CSS s).integers) ∧
      (∀ P, P ∈ (𝒞.CSS s).dom ↔ g • P ∈ (𝒞.CSS s).dom) ∧
      ∃ φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s, InducesOnChart (𝒞.CSS s) g φ.toRingEquiv ∧
        ∀ P ∈ (𝒞.CSS s).dom, (𝒞.CSS s).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (𝒞.CSS s).placeMap P) ∧

  (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ s,
    let g := SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)
    ∃ φ : 𝒞.FSS s ≃ₐ[ResidueField A] 𝒞.FSS s, InducesOnChart (𝒞.CSS s) g φ.toRingEquiv ∧
      ∀ P ∈ (𝒞.CSS s).dom, (𝒞.CSS s).placeMap (g • P) = SemilinearAut.ofAlgAut φ • (𝒞.CSS s).placeMap P) ∧

  (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → (∃ t : ZMod q, redQ q γ = CuspidalType.unipotent q t) →
    let g := SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)
    (∀ P, P ∈ (𝒞.CIg (lineInfty q)).dom ↔ g • P ∈ (𝒞.CIg (lineInfty q)).dom) ∧
    InducesOnChart (𝒞.CIg (lineInfty q)) g (RingEquiv.refl _) ∧
    (∀ P ∈ (𝒞.CIg (lineInfty q)).dom, (𝒞.CIg (lineInfty q)).placeMap (g • P) = (𝒞.CIg (lineInfty q)).placeMap P)) ∧

  (∃ ζ₀ : Idx q, ∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ ℓ,
    ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ₀ γ⁻¹)).integers = (𝒞.CIg ((redQ q γ)⁻¹ • ℓ)).integers ∧
    ((𝒞.CIg ℓ).comap (levelAutBar q M' ζ₀ γ⁻¹)).dom = (𝒞.CIg ((redQ q γ)⁻¹ • ℓ)).dom ∧
    ∀ s, ((𝒞.An ℓ s).comap (levelAutBar q M' ζ₀ γ⁻¹)).dom = (𝒞.An ((redQ q γ)⁻¹ • ℓ) s).dom)

end SemistableCovering

end ModularCurve.FullLevel

end
