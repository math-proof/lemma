import Mathlib
import Instance.ModularCurve_JHNeronObjectAtP
import Def.ModularCurve_JHPlaceSpecialization

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace ModularCurve

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

namespace JHPlaceSpecialization

namespace ProlongationDatum

variable {P : JHPlaceSpecialization p M H hpM A}
variable {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

noncomputable def chartClosure (S : Set ↥(xHFunctionFieldBar M H)) : Subring ↥(xHFunctionFieldBar M H) :=
  Subring.closure S

def chartLocalSetFst (R : ProlongationDatum P θ) (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (S : Set ↥(xHFunctionFieldBar M H)) : Set ↥(xHFunctionFieldBar M H) :=
  {f | ∃ (g u : ↥(xHFunctionFieldBar M H)) (_ : g ∈ chartClosure S) (_ : u ∈ chartClosure S) (hu₁ : u ∈ R.R₁.integers),
      ¬ v.HasValue (R.R₁.residue ⟨u, hu₁⟩) (0 : (ResidueField ↥A)) ∧ f * u = g}

def ChartEtaleAt (R : ProlongationDatum P θ) (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (S : Set ↥(xHFunctionFieldBar M H)) : Prop :=
  ∃ (z : ↥(xHFunctionFieldBar M H)) (m : Polynomial ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
    z ∈ S ∧
    (∃ hz₂ : z ∈ R.R₂.integers, ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧
      ((R.R₂.residue ⟨z, hz₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)).coeff n ≠ 0) ∧
    IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range α ∪ {z}) = ⊤ ∧
    m.Monic ∧ m.natDegree = p + 1 ∧
    (m.map α.toRingHom).eval z = 0 ∧
    (∀ i : ℕ, α (m.coeff i) ∈ Subring.closure S) ∧
    ∀ h : (Polynomial.derivative (m.map α.toRingHom)).eval z ∈ R.R₁.integers,
      ¬ v.HasValue (R.R₁.residue ⟨_, h⟩) (0 : (ResidueField ↥A))

end ProlongationDatum

end JHPlaceSpecialization

end ModularCurve
