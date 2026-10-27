import Def.Geometry.Euclidean.Kinematics
import Initialize.Tactic.Attr.Basic


/--
Central potential: \(E_p=C/r\).
-/
@[path]
private lemma main
  (C r : ℝ) :
-- imply
  central_potential C r = C / r := by
-- proof
  rfl


-- created on 2026-09-29
