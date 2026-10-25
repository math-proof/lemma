/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
import Structure.NumberTheory.ImaginaryQuadraticDiscriminant
set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/


namespace ImaginaryQuadraticDiscriminant

/-- Constructor for a fundamental imaginary quadratic discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hfund : MetaMathlibExt.IsFundamentalDiscriminant D) :
    IsFundamentalImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hfund⟩

end ImaginaryQuadraticDiscriminant
