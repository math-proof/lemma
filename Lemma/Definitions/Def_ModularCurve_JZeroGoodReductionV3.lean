import Mathlib
import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_ModularCurve_SpecializationWitness
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_ModularCurve_JZeroGoodReductionV2

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve IsLocalRing

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp

attribute [local instance] ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp
variable [Module HeckeAlg (JZero N)]

variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

variable (A) (ℓ) (hℓ) (N) in

structure JZeroGoodReductionSpecialization_alt where

  sp : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  F : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
    →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  hsurj : Function.Surjective sp

  hecke_comm : ∀ (T : HeckeAlg) (x : JZero N), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero N, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt σ ℓ →
    ∀ x : JZero N, sp (σ • x) = F (sp x)

  injective_torsion : ∀ (p : ℕ), ¬ ℓ ∣ p → ∀ (x : JZero N),
    (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0

  sfr : SpecialFibreRelation
    (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ F

namespace JZeroGoodReductionSpecialization_alt

theorem hgen (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    (q : Nat.Primes) (a : JZero N) (ha : D.sp a = 0) :
    D.sp (heckeGen q • a) = 0 := by
  rw [D.hecke_comm, ha, smul_zero]

theorem toIsSpecialization (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
      (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      A ℓ D.sp D.F where
  hecke_comm := D.hecke_comm
  inertia_comm := D.inertia_comm
  frobenius_comm := D.frobenius_comm
  injective_torsion := fun x hx hker => D.injective_torsion p hℓp x hx hker

theorem toSpecializationExistsBody (D : JZeroGoodReductionSpecialization_alt A ℓ hℓ N)
    {p : ℕ} (hℓp : ¬ ℓ ∣ p) :
    IsSpecialization (K := ℚ) (L := Qbar) p (JZero N)
        (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) A ℓ D.sp D.F
      ∧ SpecialFibreRelation
          (J' := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) ℓ hℓ D.F :=
  ⟨D.toIsSpecialization hℓp, D.sfr⟩

end JZeroGoodReductionSpecialization_alt

end ModularCurve

end
