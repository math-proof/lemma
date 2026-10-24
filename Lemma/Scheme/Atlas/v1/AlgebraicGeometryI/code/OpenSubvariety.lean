import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.OpenSubvariety
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry

/--
[isSeparated_openSubscheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean)
-/
@[path]
lemma isSeparated_openSubscheme
  {S : Scheme.{u}}
  {X : Scheme.{u}}
  [X.IsSeparated]
  {U : X.Opens} :
-- imply
  Scheme.IsSeparated (↑U : Scheme) := by
-- proof
  constructor
  rw [show terminal.from (↑U : Scheme) = U.ι ≫ terminal.from X from terminal.hom_ext _ _]
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[locallyOfFiniteType_openSubscheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean)
-/
@[path]
lemma locallyOfFiniteType_openSubscheme
  {S : Scheme.{u}}
  {X : Scheme.{u}}
  [X.Over S]
  {U : X.Opens}
  [LocallyOfFiniteType (X ↘ S)] :
-- imply
  LocallyOfFiniteType ((↑U : Scheme) ↘ S) := by
-- proof
  show LocallyOfFiniteType (U.ι ≫ (X ↘ S))
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[quasiCompact_openSubscheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean)
-/
@[path]
lemma quasiCompact_openSubscheme
  {S : Scheme.{u}}
  {X : Scheme.{u}}
  [X.Over S]
  {U : X.Opens}
  [IsLocallyNoetherian S]
  [LocallyOfFiniteType (X ↘ S)]
  [QuasiCompact (X ↘ S)] :
-- imply
  QuasiCompact ((↑U : Scheme) ↘ S) := by
-- proof
  show QuasiCompact (U.ι ≫ (X ↘ S))
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry

/--
[isAlgebraicVariety_openSubscheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean)
-/
@[path]
lemma isAlgebraicVariety_openSubscheme
  {S : Scheme.{u}}
  {X : Scheme.{u}}
  [X.Over S]
  [IsLocallyNoetherian S]
  [hX : IsAlgebraicVariety (S := S) X]
  {U : X.Opens} :
-- imply
  @IsAlgebraicVariety S (↑U : Scheme) (openSubschemeOver X U) ‹_› where isReduced :=
-- proof
  isReduced_openSubscheme X U
    isSeparated := isSeparated_openSubscheme X U
    locallyOfFiniteType := locallyOfFiniteType_openSubscheme X U
    quasiCompact := quasiCompact_openSubscheme X U

end AlgebraicGeometry


-- created on 2026-10-23
