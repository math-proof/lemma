import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ProjectiveDefinitions
open AlgebraicGeometry CategoryTheory ProjectiveDefinitions


namespace ProjectiveDefinitions

/--
[ProjectiveSpace.isSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma ProjectiveSpace.isSeparated
  {k : Type u}
  [CommRing k]
  {n : ℕ} :
-- imply
  Scheme.IsSeparated (ProjectiveSpace k n) := by
-- proof
  unfold ProjectiveSpace
  infer_instance

end ProjectiveDefinitions

namespace ProjectiveDefinitions

/--
[IsProjectiveVariety.isQuasiProjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma IsProjectiveVariety.isQuasiProjective
  {k : Type u}
  [CommRing k]
  {X : Scheme}
-- given
  (h : IsProjectiveVariety k X) :
-- imply
  IsQuasiProjectiveVariety k X := by
-- proof
  obtain ⟨n, ι, hι⟩ := h
  exact ⟨n, X, ι, hι, 𝟙 X, inferInstance⟩

end ProjectiveDefinitions

namespace ProjectiveDefinitions

/--
[projectiveSpace_isProjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma projectiveSpace_isProjective
  {k : Type u}
  [CommRing k]
  {n : ℕ} :
-- imply
  IsProjectiveVariety k (ProjectiveSpace k n) :=
-- proof
  ⟨n, 𝟙 _, inferInstance⟩

end ProjectiveDefinitions

namespace ProjectiveDefinitions

/--
[projectiveSpace_isQuasiProjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma projectiveSpace_isQuasiProjective
  {k : Type u}
  [CommRing k]
  {n : ℕ} :
-- imply
  IsQuasiProjectiveVariety k (ProjectiveSpace k n) :=
-- proof
  (projectiveSpace_isProjective k n).isQuasiProjective

end ProjectiveDefinitions

namespace ProjectiveDefinitions

/--
[IsProjectiveVariety.of_closedImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma IsProjectiveVariety.of_closedImmersion
  {k : Type u}
  [CommRing k]
  {X Y : Scheme}
  {ι : X ⟶ Y}
  [hι : IsClosedImmersion ι]
-- given
  (hY : IsProjectiveVariety k Y) :
-- imply
  IsProjectiveVariety k X := by
-- proof
  obtain ⟨n, j, hj⟩ := hY
  exact ⟨n, ι ≫ j, inferInstance⟩

end ProjectiveDefinitions

namespace ProjectiveDefinitions

/--
[IsQuasiProjectiveVariety.of_openImmersion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveDefinitions.lean)
-/
@[path]
lemma IsQuasiProjectiveVariety.of_openImmersion
  {k : Type u}
  [CommRing k]
  {X Y : Scheme}
  {j : X ⟶ Y}
  [hj : IsOpenImmersion j]
-- given
  (hY : IsQuasiProjectiveVariety k Y) :
-- imply
  IsQuasiProjectiveVariety k X := by
-- proof
  obtain ⟨n, Z, ι, hι, f, hf⟩ := hY
  exact ⟨n, Z, ι, hι, j ≫ f, inferInstance⟩

end ProjectiveDefinitions


-- created on 2026-10-23
