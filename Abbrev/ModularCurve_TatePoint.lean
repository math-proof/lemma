import Instance.ModularCurve_TateFormal
import Instance.ModularCurve_PhiGen
import Structure.WeierstrassCurve_VeluQuotientMap

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

namespace ModularCurve.TatePoint

abbrev Qbar : Type := AlgebraicClosure ℚ

abbrev H : Type := HahnSeries ℚ Qbar

section TatePoint

variable (K : Type) [Field K] [Algebra ℚ K]
variable (p : ℕ) [Fact (Nat.Prime p)] [NeZero p] (ζ : Kˣ)


variable (veluSlotSet : Fin (p + 1) → Finset (LaurentSeries K × LaurentSeries K))


variable (instQ : ∀ i, (slotQuotient K p veluSlotSet i).IsElliptic)


end TatePoint

end ModularCurve.TatePoint

end
