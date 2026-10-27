import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionSiteGeometry
open StatMech StatMech.FrontierD


/--
[fkRectOnsDirStep_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionSiteGeometry.lean)
-/
@[path]
private lemma fkRectOnsDirStep_cast_eq
  {M N : ℕ}
  {mu : Fin 4}
  {s : ZMod M × ZMod M}
-- given
  (h : M = N) :
-- imply
  Equiv.cast (congrArg (fun n => ZMod n × ZMod n) h) (ons_dirStep M mu s) = ons_dirStep N mu (Equiv.cast (congrArg (fun n => ZMod n × ZMod n) h) s) := by
-- proof
  apply StatMech.FrontierD.fkRectOnsDirStep_cast h mu s

/--
[fkRectBlackOrbitRibbonSubdivisionSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionSiteGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitRibbonSubdivisionSite_succ_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d} :
-- imply
  fkRectBlackOrbitRibbonSubdivisionSite R omega d (fkRectFinSigmaSucc (fun i => onsAnisotropicStepScale (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d i)) (fkRectBlackOrbitRibbonSubdivisionStepScale_pos R omega d) z) = ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1) (fkRectBlackOrbitRibbonSubdivisionSite R omega d z) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitRibbonSubdivisionSite_succ R omega d z


-- created on 2026-10-23
