import Mathlib
import Structure.ModularCurve_JZeroNeronObjectAtP
import Abbrev.ModularCurve_IgusaScheme
import Structure.AlgebraicCurve_CurveModel
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Structure.AlgebraicGeometry_RelEffCartierDiv
import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
import Structure.ModularCurve_JZeroNeronObjectAtP_LevelModel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing AlgebraicGeometry.RelPicard

noncomputable section

namespace ModularCurve.JZeroNeronObjectAtP


namespace LevelModel

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

attribute [instance] LevelModel.eeta₀_iso LevelModel.Meta₀_chart_nonempty


abbrev toκ (M : LevelModel N₀ p A) : baseRing p →+* ResidueField ↥A := (residue ↥A).comp M.ρ


end LevelModel

end ModularCurve.JZeroNeronObjectAtP

end
