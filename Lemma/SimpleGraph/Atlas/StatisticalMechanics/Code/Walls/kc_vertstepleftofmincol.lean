import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_vertstepleftofmincol
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc_vertStep_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_vertstepleftofmincol.lean)
-/
@[path]
private lemma kc_vertStep_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc_vertStep_dir e hv

/--
[kc_vertStep_left_of_minCol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_vertstepleftofmincol.lean)
-/
@[path]
private lemma kc_vertStep_left_of_minCol_eq
  {K : Set (Site 2)}
  {m : ℤ}
  {e : Dart}
-- given
  (hm : ∀ w ∈ K, m ≤ w 0)
  (he : IsBoundaryDart K e)
  (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
  (hcol : (dartFace e) 0 ≤ m - 1) :
-- imply
  e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Walls.kc_vertStep_left_of_minCol m hm he hvert hcol


-- created on 2026-10-23
