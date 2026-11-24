module
public import Mathlib
public import Structure.ModularCurve_JZeroNeronObjectAtP
public import Abbrev.ModularCurve_IgusaScheme
public import Structure.AlgebraicCurve_CurveModel
public import Instance.AlgebraicGeometry_RelativePicardFunctor
public import Structure.AlgebraicGeometry_RepresentsRelSubPic
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
public import Abbrev.AlgebraicGeometry_IdealSheafModule
public import Structure.AlgebraicGeometry_RelEffCartierDiv
public import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
public import Structure.ModularCurve_JZeroNeronObjectAtP_LevelModel
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing AlgebraicGeometry.RelPicard


public section

noncomputable section

namespace ModularCurve.JZeroNeronObjectAtP


namespace LevelModel

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

attribute [instance] LevelModel.eeta₀_iso LevelModel.Meta₀_chart_nonempty


abbrev toκ (M : LevelModel N₀ p A) : baseRing p →+* ResidueField ↥A := (residue ↥A).comp M.ρ


end LevelModel

end ModularCurve.JZeroNeronObjectAtP

end
