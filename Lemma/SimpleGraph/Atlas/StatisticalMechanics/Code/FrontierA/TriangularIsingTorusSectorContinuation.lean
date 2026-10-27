import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
open StatMech StatMech.FrontierA


/--
[triangularTorusSpinScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean)
-/
@[path]
private lemma triangularTorusSpinScalePolynomial_eval_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Complex}
  {a b : Fin 2}
  {t : Complex} :
-- imply
  (triangularTorusSpinScalePolynomial L weight a b).eval t = triangularTorusWeightedSpinCharacterSum L (fun edge => t * weight edge) a b := by
-- proof
  apply StatMech.FrontierA.triangularTorusSpinScalePolynomial_eval L weight a b t

/--
[triangularTorusEdgeWeight_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean)
-/
@[path]
private lemma triangularTorusEdgeWeight_scale_eq
  {L : Nat}
  {t1 t2 t3 s : Complex} :
-- imply
  (fun edge => s * triangularTorusEdgeWeight L t1 t2 t3 edge) = triangularTorusEdgeWeight L (s * t1) (s * t2) (s * t3) := by
-- proof
  apply StatMech.FrontierA.triangularTorusEdgeWeight_scale L t1 t2 t3 s

/--
[triangularTorusKWMatrix_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean)
-/
@[path]
private lemma triangularTorusKWMatrix_scale_eq
  {L : Nat}
  {t1 t2 t3 rho u v s : Complex} :
-- imply
  triangularTorusKWMatrix L (s * t1) (s * t2) (s * t3) rho u v = s • triangularTorusKWMatrix L t1 t2 t3 rho u v := by
-- proof
  apply StatMech.FrontierA.triangularTorusKWMatrix_scale L t1 t2 t3 rho u v s

/--
[triangularTorus_sector_sq_eq_det_of_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorContinuation.lean)
-/
@[path]
private lemma triangularTorus_sector_sq_eq_det_of_interval_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho u v : Complex}
  {a b : Fin 2}
-- given
  (hinterval : ∃ delta : Real, 0 < delta ∧ ∀ r : Real, r ∈ Set.Ioo 0 delta → triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L ((r : Complex) * t1) ((r : Complex) * t2) ((r : Complex) * t3)) a b ^ 2 = (1 - triangularTorusKWMatrix L ((r : Complex) * t1) ((r : Complex) * t2) ((r : Complex) * t3) rho u v).det) :
-- imply
  triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L t1 t2 t3) a b ^ 2 = (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det := by
-- proof
  apply StatMech.FrontierA.triangularTorus_sector_sq_eq_det_of_interval L t1 t2 t3 rho u v a b hinterval


-- created on 2026-10-23
