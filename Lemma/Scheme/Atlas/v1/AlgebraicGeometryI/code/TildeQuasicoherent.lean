import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.TildeQuasicoherent
open AlgebraicGeometry CategoryTheory


/--
[tilde_isQuasicoherent_cor16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TildeQuasicoherent.lean)
-/
@[path]
lemma tilde_isQuasicoherent_cor16
  {R : CommRingCat.{u}}
  {M : ModuleCat.{u} R} :
-- imply
  (tilde M).IsQuasicoherent :=
-- proof
  inferInstance


-- created on 2026-10-23
