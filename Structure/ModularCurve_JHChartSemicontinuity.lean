import Mathlib
import Instance.ModularCurve_JHNeronObjectAtP
import Structure.ModularCurve_JHPlaceSpecialization
import Def.ModularCurve_JHChartSemicontinuity

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


structure IsCuspChartFstAt (R : ProlongationDatum P θ) (α : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (S : Set ↥(xHFunctionFieldBar M H)) : Prop where
  integral : ∀ s ∈ S, s ∈ R.R₁.integers
  regular : ∀ (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ S), (R.R₁.residue ⟨s, integral s hs⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring
  regularOver : ∀ s ∈ S, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), P.reduceFst α hα W = v → s ∈ W.toValuationSubring
  nIncl : ∀ φ : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), α φ ∈ R.R₁.integers →
    (∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), P.sp u₀ = v → φ ∈ u₀.toValuationSubring) →
    ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ S) (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ S),
      ¬ v.HasValue (R.R₁.residue ⟨e, integral e he⟩) (0 : (ResidueField ↥A)) ∧ α φ * e = s
  etale : R.ChartEtaleAt α v S
  separates : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
    IsZeroSide (p := p) (M := M) (H := H) (A := A) W → P.reduceFst α hα W = v →
      ∃ (u : ↥(xHFunctionFieldBar M H)) (hu : u ∈ S), ¬ v.HasValue (R.R₁.residue ⟨u, integral u hu⟩) (0 : (ResidueField ↥A)) ∧ 0 < W.ord u

end ProlongationDatum

end JHPlaceSpecialization

end ModularCurve
