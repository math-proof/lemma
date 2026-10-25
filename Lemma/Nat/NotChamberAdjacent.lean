import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
open CoxeterComplex


namespace Definitions
end Definitions
namespace CoxeterComplex

/--
[chamberAdjacent_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean)
-/
@[path]
private lemma chamberAdjacent_irrefl
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group} :
-- imply
  ¬ChamberAdjacent M w w :=
-- proof
  fun ⟨h, _⟩ => h rfl

end CoxeterComplex

namespace CoxeterComplex

/--
[isGallery_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean)
-/
@[path]
private lemma isGallery_nil
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  IsGallery M ([] : List M.Group) :=
-- proof
  trivial

end CoxeterComplex

namespace CoxeterComplex

/--
[isGallery_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean)
-/
@[path]
private lemma isGallery_singleton
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group} :
-- imply
  IsGallery M [w] :=
-- proof
  trivial

end CoxeterComplex

namespace CoxeterComplex

/--
[isGallery_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean)
-/
@[path]
private lemma isGallery_cons
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w w' : M.Group}
  {rest : List M.Group}
-- given
  (h : IsGallery M (w :: w' :: rest)) :
-- imply
  ChamberAdjacent M w w' ∧ IsGallery M (w' :: rest) :=
-- proof
  h

end CoxeterComplex

namespace CoxeterComplex

/--
[Simplex.isFaceOf_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean)
-/
@[path]
private lemma Simplex.isFaceOf_refl
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {σ : Simplex M} :
-- imply
  σ.IsFaceOf M σ :=
-- proof
  ⟨Finset.Subset.refl _, ⟨1, by simp, Subgroup.one_mem _⟩⟩

end CoxeterComplex


-- created on 2026-10-24
