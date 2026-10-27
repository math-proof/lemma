import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.SerreCoherentSheavesProjVar
open AlgebraicGeometry CategoryTheory TensorProduct Corollary19


namespace Corollary19

/--
[pic_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreCoherentSheavesProjVar.lean)
-/
@[path]
lemma pic_comm
  {R : Type u}
  [CommSemiring R]
  {a b : CommRing.Pic R} :
-- imply
  a * b = b * a :=
-- proof
  mul_comm a b
/-- Two invertible modules represent the same Picard class iff they are
isomorphic as `R`-modules. -/
end Corollary19



-- created on 2026-10-23
