import Mathlib
import Initialize.Tactic.Attr.Basic
open AlgebraicGeometry CategoryTheory


/--
[prop27_isProper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop27FiniteMap.lean)
-/
@[path]
lemma prop27_isProper
  {k : Type u}
  [Field k]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsProper (Y ↘ Spec (.of k))]
  {f : X ⟶ Y}
  [f.IsOver (Spec (.of k))] :
-- imply
  IsProper f := by
-- proof
  have h : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k) := HomIsOver.comp_over
  haveI : IsProper (f ≫ (Y ↘ Spec (.of k))) := h ▸ inferInstance
  exact IsProper.of_comp f (Y ↘ Spec (.of k))
/-- Lemma 29: for a dominant proper morphism of integral schemes, the induced map to
the normalization of `Y` is an isomorphism. -/


-- created on 2026-10-23
