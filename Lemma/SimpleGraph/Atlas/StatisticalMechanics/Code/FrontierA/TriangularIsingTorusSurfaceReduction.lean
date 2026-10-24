import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceReduction
open StatMech StatMech.FrontierA


/--
[triangularTorus_sector_sq_eq_det_of_surface_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSurfaceReduction.lean)
-/
@[path]
private lemma triangularTorus_sector_sq_eq_det_of_surface_base_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2}
-- given
  (hbase : ∀ w : Sym2 (ZMod L × ZMod L) → Complex, (1 - kwGraphTransition (triangularTorusGraph L) w (triangularTorusGraphPhase L rho 1 1)).det = surfaceQuadraticEvenPolynomial (triangularTorusGraph L) (triangularTorusSurfaceEdgeClass L) ((fun _ => (1 : Fin 2)), (fun _ => (1 : Fin 2))) w ^ 2) :
-- imply
  triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 = (1 - triangularTorusKWMatrix L t1 t2 t3 rho (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.FrontierA.triangularTorus_sector_sq_eq_det_of_surface_base L t1 t2 t3 rho a b hbase


-- created on 2026-10-23
