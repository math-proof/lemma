import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.CAT0
open IsCAT0FourPoint


/--
[isCAT0FourPoint_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
private lemma isCAT0FourPoint_iff_eq
  {X : Type u} [MetricSpace X] :
-- imply
  IsCAT0FourPoint X ↔
      ∀ x y z w : X,
        dist x z ^ 2 + dist y w ^ 2 ≤
          dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2 := by
-- proof
  apply isCAT0FourPoint_iff

/--
[of_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
private lemma of_isometry_eq
  {X : Type u} [MetricSpace X]
  {Y : Type v} [MetricSpace Y]
  {f : X → Y}
-- given
  (hY : IsCAT0FourPoint Y)
  (hf : Isometry f) :
-- imply
  IsCAT0FourPoint X := by
-- proof
  apply IsCAT0FourPoint.of_isometry hY hf

/--
[iff_of_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
private lemma iff_of_isometryEquiv_eq
  {X : Type u} [MetricSpace X]
  {Y : Type v} [MetricSpace Y]
-- given
  (e : X ≃ᵢ Y) :
-- imply
  IsCAT0FourPoint X ↔ IsCAT0FourPoint Y := by
-- proof
  apply IsCAT0FourPoint.iff_of_isometryEquiv e

/--
[of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
private lemma of_subsingleton_eq
  {X : Type u} [MetricSpace X] [Subsingleton X] :
-- imply
  IsCAT0FourPoint X := by
-- proof
  apply IsCAT0FourPoint.of_subsingleton X


-- created on 2026-10-20
