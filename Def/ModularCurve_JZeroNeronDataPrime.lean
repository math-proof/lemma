import Mathlib
import Def.ModularCurve_JZeroNeronData
import Lemma.ModularCurve.HeckeModule
import Def.ModularCurve_HeckeInputsAll
import Def.FLTPrelim_Ramification
import Def.GaloisRep_Flat
import Structure.ModularCurve_JZeroNeronDataPrime

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open ValuationSubring


theorem mem_inertiaInvariantPoints {p : ℕ} [NeZero p] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {x : JZero p} : x ∈ inertiaInvariantPoints p A ↔ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  Iff.rfl


def HasJZeroNeronDataPrime (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), Nonempty (JZeroNeronDataPrime p A hA)

section RationalPoints

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

theorem fixedPoints_le_inertiaInvariantPoints :
    FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p) ≤ inertiaInvariantPoints p A :=
  fun _ hx σ _ => hx σ

def JZeroNeronDataPrime.redComponentRat (D : JZeroNeronDataPrime p A hA) :
    ↥(FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p)) →+ D.Φ :=
  D.redComponent.comp (AddSubgroup.inclusion (fixedPoints_le_inertiaInvariantPoints p A))

def JZeroNeronDataPrime.M0 (D : JZeroNeronDataPrime p A hA) :
    AddSubgroup ↥(FixedPoints.addSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero p)) :=
  (D.redComponentRat p A hA).ker

end RationalPoints

end ModularCurve

end
