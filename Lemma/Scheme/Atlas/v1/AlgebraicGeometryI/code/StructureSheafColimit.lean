import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.StructureSheafColimit
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite Lec6 Lec6.RegularFunctions


namespace Lec6.RegularFunctions

/--
[isFraction_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean)
-/
@[path]
lemma isFraction_iff
  {R : Type*}
  [CommRing R]
  {U : Opens (PrimeSpectrum.Top R)}
  {f : Π x : U, StructureSheaf.Localizations R x.1} :
-- imply
  StructureSheaf.IsFraction f ↔ ∃ (g : R) (h : R), ∀ x : U, ∃ (hx : h ∉ x.1.asIdeal), f x = LocalizedModule.mk g ⟨h, hx⟩ := by
-- proof
  rfl

end Lec6.RegularFunctions

namespace Lec6.RegularFunctions

/--
[stalk_eq_colimit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean)
-/
@[path]
lemma stalk_eq_colimit
  {X : TopCat}
  {F : X.Presheaf CommRingCat}
  {x : X} :
-- imply
  F.stalk x = (TopCat.Presheaf.stalkFunctor CommRingCat x).obj F :=
-- proof
  rfl

end Lec6.RegularFunctions

namespace Lec6.RegularFunctions

/--
[functionField_eq_stalk_genericPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean)
-/
@[path]
lemma functionField_eq_stalk_genericPoint
  {X : Scheme}
  [IrreducibleSpace X] :
-- imply
  X.functionField = X.presheaf.stalk (genericPoint X) :=
-- proof
  rfl

end Lec6.RegularFunctions

namespace Lec6.RegularFunctions

/--
[functionField_germ_injective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean)
-/
@[path]
lemma functionField_germ_injective'
  {X : Scheme}
  [IsIntegral X]
  {U : X.Opens}
  [Nonempty U] :
-- imply
  Function.Injective (X.germToFunctionField U) :=
-- proof
  Scheme.germToFunctionField_injective X U

end Lec6.RegularFunctions


-- created on 2026-10-23
