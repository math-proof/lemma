module

public import Mathlib
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.TildeQuasicoherent

public section

open AlgebraicGeometry CategoryTheory


/--
[tilde_isQuasicoherent_cor16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TildeQuasicoherent.lean)
-/
public theorem tilde_isQuasicoherent_cor16
  {R : CommRingCat.{u}}
  {M : ModuleCat.{u} R} :
-- imply
  (tilde M).IsQuasicoherent :=
-- proof
  inferInstance


-- created on 2026-10-23
