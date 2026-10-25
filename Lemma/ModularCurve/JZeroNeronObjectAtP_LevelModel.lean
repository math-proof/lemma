import Mathlib
import Def.ModularCurve_JZeroNeronObjectAtP
import Abbrev.ModularCurve_IgusaScheme
import Lemma.AlgebraicCurve.CurveModel
import Def.AlgebraicGeometry_RelativePicardFunctor
import Lemma.AlgebraicGeometry.RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Abbrev.AlgebraicGeometry_IdealSheafModule
import Lemma.AlgebraicGeometry.RelEffCartierDiv
import Lemma.AlgebraicGeometry.RelEffCartierDivOfPoint
import Structure.ModularCurve_JZeroNeronObjectAtP_LevelModel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing AlgebraicGeometry.RelPicard

noncomputable section

namespace ModularCurve.JZeroNeronObjectAtP


namespace LevelModel

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}


abbrev σA (M : LevelModel N₀ p A) : Spec (CommRingCat.of ↥A) ⟶ base p := Spec.map (CommRingCat.ofHom M.ρ)


theorem barPt_σA (M : LevelModel N₀ p A) : barPt A ≫ M.σA = genPt p := by
  simp only [barPt, genPt, σA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, M.hρ]

abbrev law (M : LevelModel N₀ p A) : RelativeGroupLaw (baseRing p) M.D₀.toBase :=
  RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (IgusaScheme.igusaTo N₀ p) M.ε₀) M.rep

def toLevelData (M : LevelModel N₀ p A) : LevelData N₀ p A where
  σA := M.σA
  hσA := M.barPt_σA
  X := M.D₀.P
  f := M.D₀.toBase
  L := M.law
  pts := M.pts
  ptsSp := M.ptsSp

end LevelModel

end ModularCurve.JZeroNeronObjectAtP

end
