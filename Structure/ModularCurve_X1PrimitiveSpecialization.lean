import Mathlib
import Def.FLTPrelim_Ramification
import Def.ModularCurve_X1Diamond
import Instance.EllipticCurve_TateModule
import Def.ModularCurve_X1PrimitiveSpecialization

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree


variable (M : ℕ)


end NormFree

section Datum

variable (M₀ q c : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] (π : P →+* k)

structure X1PrimitiveSpecialization where

  igusaDiamond : ℕ → (x1FunctionFieldC k (M₀ * q ^ c) ≃ₐ[k] x1FunctionFieldC k (M₀ * q ^ c))

  igusaDiamond_apply_eq : ∀ (d : ℕ) (y y' : LaurentSeries P)
    (hy : coeffMap P.subtype y ∈ x1FunctionFieldBar (M₀ * q ^ c))
    (hy' : coeffMap P.subtype y' ∈ x1FunctionFieldBar (M₀ * q ^ c)),
    diamondAutBar (M₀ * q ^ c) d ⟨coeffMap P.subtype y, hy⟩ = ⟨coeffMap P.subtype y', hy'⟩ →
      ∀ (hk : coeffMap π y ∈ x1FunctionFieldC k (M₀ * q ^ c))
        (hk' : coeffMap π y' ∈ x1FunctionFieldC k (M₀ * q ^ c)),
        igusaDiamond d ⟨coeffMap π y, hk⟩ = ⟨coeffMap π y', hk'⟩

  spInf : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spZero : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spInf_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ (y : primitivePart M₀ q c)
    (h : σ • (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c), spInf ⟨_, h⟩ = spInf y

  spInf_diamondOneBar : ∀ (d : ℕ) (y : primitivePart M₀ q c)
    (h : diamondOneBar (M₀ * q ^ c) d (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c),
    spInf ⟨_, h⟩ = SemilinearAut.ofAlgAut (igusaDiamond d) • spInf y

  spZero_diamondOneBar_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ u : ℕ, u ≡ 1 [MOD M₀] →
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ c) = 1 → σ ζ = ζ ^ u) →
      ∀ (y : primitivePart M₀ q c)
        (h : diamondOneBar (M₀ * q ^ c) u (σ • (y : JOne (M₀ * q ^ c))) ∈ primitivePart M₀ q c),
        spZero ⟨_, h⟩ = spZero y

  eq_zero_of_forall_eq_zero : ∀ (p : ℕ) [Fact p.Prime], p ≠ q →
    ∀ (y : TateModule p (JOne (M₀ * q ^ c)))
      (h : ∀ n, (y : ℕ → JOne (M₀ * q ^ c)) n ∈ primitivePart M₀ q c),
      (∀ n, spInf ⟨_, h n⟩ = 0) → (∀ n, spZero ⟨_, h n⟩ = 0) → y = 0

end Datum

end ModularCurve

end
