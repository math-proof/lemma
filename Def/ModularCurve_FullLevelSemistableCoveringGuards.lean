import Lemma.ModularCurve.FullLevelSemistableCovering
import Lemma.AlgebraicCurve.Repartitions
import Class.AlgebraicCurve_IsCurveOver

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {SS : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def GenusClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + (Nat.card (CuspidalType.ProjLine q) + SS.card) =
    ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FIg ℓ) +
      ∑ s ∈ SS.attach, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FSS s) +
        Nat.card (CuspidalType.ProjLine q) * SS.card + 1

def HasDiscFibres {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A (fieldBar q M') Fbar) : Prop :=
  ∀ Q : Place (IsLocalRing.ResidueField A) Fbar, Q ∉ C.nodes →
    ∃ (T : ↥(fieldBar q M')) (hT : T ∈ C.integers), C.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (C.residue ⟨T, hT⟩) = 1 ∧
      (∀ P ∈ C.dom, C.placeMap P = Q → T ∈ P.toValuationSubring ∧
        ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
      ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
        ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ C.dom ∧ C.placeMap P = Q ∧ P.evalAt T = c

def DiscFibreClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  (∀ ℓ, HasDiscFibres (𝒞.CIg ℓ)) ∧ ∀ s, HasDiscFibres (𝒞.CSS s)

def CurveClause (𝒞 : SemistableCovering q M' A SS) : Prop :=
  (∀ ℓ, IsCurveOver (ResidueField A) (𝒞.FIg ℓ) ∧ Algebra.EssFiniteType (ResidueField A) (𝒞.FIg ℓ)) ∧
    ∀ s, IsCurveOver (ResidueField A) (𝒞.FSS s) ∧ Algebra.EssFiniteType (ResidueField A) (𝒞.FSS s)

end SemistableCovering

end ModularCurve.FullLevel

end
