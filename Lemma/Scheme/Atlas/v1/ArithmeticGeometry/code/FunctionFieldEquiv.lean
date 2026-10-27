import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv.Part4
open AlgebraicGeometry CategoryTheory ArithmeticGeometry ArithmeticGeometry.Thm19_2


namespace ArithmeticGeometry.Thm19_2

/--
[SmProjCurve.fromSpecStalk_genericPoint_isDominant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldEquiv.lean)
-/
@[path]
lemma SmProjCurve.fromSpecStalk_genericPoint_isDominant
  {k : Type u}
  [Field k]
  [PerfectField k]
  {C : SmProjCurve k} :
-- imply
  IsDominant (C.toScheme.fromSpecStalk (genericPoint C.toScheme)) := by
-- proof
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  constructor
  show Dense (Set.range (C.toScheme.fromSpecStalk (genericPoint C.toScheme)))
  rw [show Set.range (⇑(C.toScheme.fromSpecStalk (genericPoint C.toScheme))) =
    {y | y ⤳ genericPoint C.toScheme} from Scheme.range_fromSpecStalk]
  apply Dense.mono (s₁ := {genericPoint C.toScheme})
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [Set.mem_setOf_eq, hy]
  · rw [dense_iff_closure_eq]
    exact genericPoint_closure (α := C.toScheme)

end ArithmeticGeometry.Thm19_2

namespace ArithmeticGeometry.Thm19_2

/--
[SmProjCurve.Hom.ext_of_fromSpecStalk_genericPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldEquiv.lean)
-/
@[path]
lemma SmProjCurve.Hom.ext_of_fromSpecStalk_genericPoint
  {k : Type u}
  [Field k]
  [PerfectField k]
  {C₁ C₂ : SmProjCurve k}
  {f g : C₁ ⟶ C₂}
-- given
  (h : C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ f.toSchemeHom = C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ g.toSchemeHom) :
-- imply
  f = g := by
-- proof
  have hfg : f.toSchemeHom = g.toSchemeHom := by
    haveI : IsReduced C₁.toScheme := inferInstance
    haveI : IsSeparated C₂.structureMorphism := inferInstance
    haveI : IrreducibleSpace C₁.toScheme := irreducibleSpace_of_isIntegral C₁.toScheme
    haveI := C₁.fromSpecStalk_genericPoint_isDominant k
    exact ext_of_isDominant_of_isSeparated C₂.structureMorphism
      (by rw [f.over_spec, g.over_spec]) _ h
  exact SmProjCurve.Hom.ext hfg

end ArithmeticGeometry.Thm19_2


-- created on 2026-10-23
