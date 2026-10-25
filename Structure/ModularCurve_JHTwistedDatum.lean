import Structure.ModularCurve_JHTwistType

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

structure TwistedFibreDatum {p M : ℕ} {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} {A : ValuationSubring (AlgebraicClosure ℚ)}
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) where

  unifFst : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  unifSnd : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  corrFst : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  corrSnd : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  u0 : ↥SS → (ResidueField ↥A)ˣ
  lam : ↥SS → (ResidueField ↥A)ˣ
  mu : ↥SS → (ResidueField ↥A)ˣ

section
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
  (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
  (dat : TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


end

end JHPlaceSpecialization
end ModularCurve

end
