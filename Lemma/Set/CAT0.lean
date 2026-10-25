import Mathlib
import sympy.Basic
import Theorem.Geometry.CAT0
open IsCAT0FourPoint


/--
[of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
lemma of_subsingleton
  {X : Type u} [MetricSpace X] [Subsingleton X] :
-- imply
  IsCAT0FourPoint X := by
-- proof
  intro x y z w
  have hxy : x = y := Subsingleton.elim _ _
  have hxz : x = z := Subsingleton.elim _ _
  have hxw : x = w := Subsingleton.elim _ _
  subst y
  subst z
  subst w
  simp

/--
[isCAT0FourPoint_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
lemma isCAT0FourPoint_iff
  {X : Type u} [MetricSpace X] :
-- imply
  IsCAT0FourPoint X ↔
    ∀ x y z w : X,
    dist x z ^ 2 + dist y w ^ 2 ≤
    dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2 :=
-- proof
  Iff.rfl

namespace IsCAT0FourPoint

/--
[of_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
lemma of_isometry
  {X : Type u} [MetricSpace X]
  {Y : Type v} [MetricSpace Y]
  {f : X → Y}
-- given
  (hY : IsCAT0FourPoint Y)
  (hf : Isometry f) :
-- imply
  IsCAT0FourPoint X := by
-- proof
  intro x y z w
  simpa only [hf.dist_eq] using hY (f x) (f y) (f z) (f w)

end IsCAT0FourPoint

namespace IsCAT0FourPoint

/--
[iff_of_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean)
-/
@[path]
lemma iff_of_isometryEquiv
  {X : Type u} [MetricSpace X]
  {Y : Type v} [MetricSpace Y]
-- given
  (e : X ≃ᵢ Y) :
-- imply
  IsCAT0FourPoint X ↔ IsCAT0FourPoint Y :=
-- proof
  ⟨fun hX ↦ of_isometry hX e.symm.isometry, fun hY ↦ of_isometry hY e.isometry⟩

end IsCAT0FourPoint


-- created on 2026-10-20
-- updated on 2026-10-23
