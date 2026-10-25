import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
open StatMech StatMech.FrontierA


/--
[triangularTorus_native_det_square_of_localSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusShiftedAssembly.lean)
-/
@[path]
private lemma triangularTorus_native_det_square_of_localSplit_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hphase : KWLocalAngularSplitShiftedCyclePhase (triangularTorusLocalAngularData L rho hrho) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) (triangularTorusSurfaceSpin 0 0))
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)))
  (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
-- imply
  (1 - kwGraphTransition (triangularTorusGraph L) weight (triangularTorusGraphPhase L rho 1 1)).det = surfaceQuadraticEvenPolynomial (triangularTorusGraph L) (triangularTorusSurfaceEdgeClass L) (triangularTorusSurfaceSpin 0 0) weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_native_det_square_of_localSplit L rho hrho hphase hisotropic weight

/--
[triangularTorus_sector_sq_eq_det_of_localSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusShiftedAssembly.lean)
-/
@[path]
private lemma triangularTorus_sector_sq_eq_det_of_localSplit_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hphase : KWLocalAngularSplitShiftedCyclePhase (triangularTorusLocalAngularData L rho hrho) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) (triangularTorusSurfaceSpin 0 0))
  (hisotropic : SurfaceDisjointCycleIsotropic (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))) :
-- imply
  triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 = (1 - triangularTorusKWMatrix L t1 t2 t3 rho (StatMech.Onsager.ons_spinPhase L a) (StatMech.Onsager.ons_spinPhase L b)).det := by
-- proof
  apply StatMech.FrontierA.triangularTorus_sector_sq_eq_det_of_localSplit L t1 t2 t3 rho a b hrho hphase hisotropic

/--
[triangularTorus_native_det_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusShiftedAssembly.lean)
-/
@[path]
private lemma triangularTorus_native_det_square_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
-- imply
  (1 - kwGraphTransition (triangularTorusGraph L) weight (triangularTorusGraphPhase L rho 1 1)).det = surfaceQuadraticEvenPolynomial (triangularTorusGraph L) (triangularTorusSurfaceEdgeClass L) (triangularTorusSurfaceSpin 0 0) weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_native_det_square L rho hrho weight

/--
[triangularTorus_sector_sq_eq_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusShiftedAssembly.lean)
-/
@[path]
private lemma triangularTorus_sector_sq_eq_det_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 = (1 - triangularTorusKWMatrix L t1 t2 t3 rho (StatMech.Onsager.ons_spinPhase L a) (StatMech.Onsager.ons_spinPhase L b)).det := by
-- proof
  apply StatMech.FrontierA.triangularTorus_sector_sq_eq_det L t1 t2 t3 rho a b hrho


-- created on 2026-10-23
