import Mathlib
import Lemma.ModularCurve.HeckeModule
import Lemma.ModularCurve.SpecializationWitness
import Lemma.ModularCurve.JqCoeff
import Lemma.EllipticCurve.FrobeniusTrace
import Structure.ModularCurve_JZeroGoodReductionV2
import Structure.ModularCurve_JZeroGoodReductionV3
import Notation.ModularCurve_JZeroGoodReductionV3

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve IsLocalRing

namespace ModularCurve

open scoped ModularCurve_JZeroGoodReductionV3

variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp

attribute [local instance] ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp
variable [Module HeckeAlg (JZero N)]

variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

variable (A) (ℓ) (hℓ) (N) in

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
