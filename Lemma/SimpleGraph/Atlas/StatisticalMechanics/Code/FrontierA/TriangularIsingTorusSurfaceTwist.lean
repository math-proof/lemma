import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
open StatMech StatMech.FrontierA


/--
[triangularTorusDirectionPhase_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSurfaceTwist.lean)
-/
@[path]
private lemma triangularTorusDirectionPhase_one_one_eq
  {a : Fin 6} :
-- imply
  triangularTorusDirectionPhase 1 1 a = 1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionPhase_one_one a

/--
[surfaceTwistedKacWardMatrix_triangularTorusDartEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSurfaceTwist.lean)
-/
@[path]
private lemma surfaceTwistedKacWardMatrix_triangularTorusDartEquiv_apply_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2}
  {d e : triangularTorusDart L} :
-- imply
  surfaceTwistedKacWardMatrix (triangularTorusGraph L) (triangularTorusGraphPhase L rho 1 1) (triangularTorusSurfaceEdgeClass L) (fun _ => a, fun _ => b) (triangularTorusEdgeWeight L t1 t2 t3) (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e) = if (triangularTorusDartEquiv L d).snd = (triangularTorusDartEquiv L e).fst ∧ (triangularTorusDartEquiv L d).edge ≠ (triangularTorusDartEquiv L e).edge then triangularTorusDirectionWeight t1 t2 t3 d.2 * (triangularTorusSpinDartSeamSign L a b d * triangularKacWardTurnMatrix rho d.2 e.2) else 0 := by
-- proof
  apply StatMech.FrontierA.surfaceTwistedKacWardMatrix_triangularTorusDartEquiv_apply L t1 t2 t3 rho a b d e

/--
[triangularTorusSeamKWMatrix_eq_reindex_surfaceTwisted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSurfaceTwist.lean)
-/
@[path]
private lemma triangularTorusSeamKWMatrix_eq_reindex_surfaceTwisted_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2} :
-- imply
  triangularTorusSeamKWMatrix L t1 t2 t3 rho a b = (Matrix.reindex (triangularTorusDartEquiv L).symm (triangularTorusDartEquiv L).symm) (surfaceTwistedKacWardMatrix (triangularTorusGraph L) (triangularTorusGraphPhase L rho 1 1) (triangularTorusSurfaceEdgeClass L) (fun _ => a, fun _ => b) (triangularTorusEdgeWeight L t1 t2 t3)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSeamKWMatrix_eq_reindex_surfaceTwisted L t1 t2 t3 rho a b

/--
[det_one_sub_triangularTorusSeamKWMatrix_eq_surfaceTwisted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSurfaceTwist.lean)
-/
@[path]
private lemma det_one_sub_triangularTorusSeamKWMatrix_eq_surfaceTwisted_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2} :
-- imply
  (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det = (1 - surfaceTwistedKacWardMatrix (triangularTorusGraph L) (triangularTorusGraphPhase L rho 1 1) (triangularTorusSurfaceEdgeClass L) (fun _ => a, fun _ => b) (triangularTorusEdgeWeight L t1 t2 t3)).det := by
-- proof
  apply StatMech.FrontierA.det_one_sub_triangularTorusSeamKWMatrix_eq_surfaceTwisted L t1 t2 t3 rho a b


-- created on 2026-10-23
