import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge
open StatMech StatMech.FrontierA


/--
[triangularTorusXMovement_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusXMovement_target_eq
  {L : Nat}
  {d : triangularTorusDart L} :
-- imply
  (ons_dirStep L (triangularTorusXMovementDirection d.2) d.1).1 = (d.1 - triangularTorusDirectionStep L d.2).1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusXMovement_target L d

/--
[triangularTorusYMovement_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusYMovement_target_eq
  {L : Nat}
  {d : triangularTorusDart L} :
-- imply
  (ons_dirStep L (triangularTorusYMovementDirection d.2) d.1).2 = (d.1 - triangularTorusDirectionStep L d.2).2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusYMovement_target L d

/--
[triangularTorusDirectionPhase_eq_movement_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusDirectionPhase_eq_movement_zpow_eq
  {L : Nat}
  {a b : Fin 2}
  {d : triangularTorusDart L} :
-- imply
  triangularTorusDirectionPhase (ons_spinPhase L a) (ons_spinPhase L b) d.2 = ons_spinPhase L a ^ (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) * ons_spinPhase L b ^ (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionPhase_eq_movement_zpow L a b d

/--
[triangularTorusSpinVertexGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusSpinVertexGauge_ne_zero_eq
  {L : Nat}
  {a b : Fin 2}
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusSpinVertexGauge L a b p ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSpinVertexGauge_ne_zero L a b p

/--
[triangularTorusDirectionPhase_mul_vertexGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusDirectionPhase_mul_vertexGauge_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : triangularTorusDart L} :
-- imply
  triangularTorusDirectionPhase (ons_spinPhase L a) (ons_spinPhase L b) d.2 * triangularTorusSpinVertexGauge L a b d.1 = triangularTorusSpinDartSeamSign L a b d * triangularTorusSpinVertexGauge L a b (d.1 - triangularTorusDirectionStep L d.2) := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionPhase_mul_vertexGauge L a b d

/--
[triangularTorusSpinDartGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusSpinDartGauge_ne_zero_eq
  {L : Nat}
  {a b : Fin 2}
  {d : triangularTorusDart L} :
-- imply
  triangularTorusSpinDartGauge L a b d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSpinDartGauge_ne_zero L a b d

/--
[triangularTorusKWMatrix_spin_eq_diagonalGauge_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma triangularTorusKWMatrix_spin_eq_diagonalGauge_seam_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2} :
-- imply
  triangularTorusKWMatrix L t1 t2 t3 rho (ons_spinPhase L a) (ons_spinPhase L b) = ons_diagonalGaugeMatrix (triangularTorusSpinDartGauge L a b) (triangularTorusSeamKWMatrix L t1 t2 t3 rho a b) := by
-- proof
  apply StatMech.FrontierA.triangularTorusKWMatrix_spin_eq_diagonalGauge_seam L t1 t2 t3 rho a b

/--
[det_ons_diagonalGaugeMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma det_ons_diagonalGaugeMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {M : Matrix E E Complex}
-- given
  (gauge : E -> Complex)
  (hgauge : forall e, gauge e ≠ 0) :
-- imply
  (ons_diagonalGaugeMatrix gauge M).det = M.det := by
-- proof
  apply StatMech.FrontierA.det_ons_diagonalGaugeMatrix gauge hgauge M

/--
[det_one_sub_triangularTorusKWMatrix_spin_eq_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean)
-/
@[path]
private lemma det_one_sub_triangularTorusKWMatrix_spin_eq_seam_eq
  {L : Nat}
  [Fact (2 < L)]
  {t1 t2 t3 rho : Complex}
  {a b : Fin 2} :
-- imply
  (1 - triangularTorusKWMatrix L t1 t2 t3 rho (ons_spinPhase L a) (ons_spinPhase L b)).det = (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det := by
-- proof
  apply StatMech.FrontierA.det_one_sub_triangularTorusKWMatrix_spin_eq_seam L t1 t2 t3 rho a b


-- created on 2026-10-23
