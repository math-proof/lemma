-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_HeckeTower.lean: instance decls only.
import Lemma.AlgebraicCurve.Correspondence
import Instance.AlgebraicCurve_IsCurveOver
import Abbrev.CerednikDrinfeld_HeckeTower

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve


namespace TowerData

variable {Fbase : Type} [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] (T : TowerData q q' Fbase)

instance instFieldObj : ∀ j : Obj q q', Field (T.objField j)
  | none => inferInstanceAs (Field Fbase)
  | some ℓ => inferInstanceAs (Field (T.F ℓ))

instance instAlgebraObj : ∀ j : Obj q q', Algebra (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra (AlgebraicClosure ℚ) (T.F ℓ))

instance instCurveObj [IsCurveOver (AlgebraicClosure ℚ) Fbase] : ∀ j : Obj q q', IsCurveOver (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (IsCurveOver (AlgebraicClosure ℚ) (T.F ℓ))

instance instEssFiniteTypeObj [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase] :
    ∀ j : Obj q q', Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.objField j)
  | none => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbase)
  | some ℓ => inferInstanceAs (Algebra.EssFiniteType (AlgebraicClosure ℚ) (T.F ℓ))

end TowerData

end HeckeTower
end CerednikDrinfeld
