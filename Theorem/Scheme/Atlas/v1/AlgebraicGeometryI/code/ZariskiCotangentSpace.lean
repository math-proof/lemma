module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.v1.Atlas.AlgebraicGeometryI.code.ZariskiCotangentSpace.Part2

public section

open IsLocalRing


/--
[ZariskiCotangentSpace.eq_maximalIdeal_cotangent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiCotangentSpace.lean)
-/
@[path]
public theorem eq_maximalIdeal_cotangent
  {R : Type u}
  [CommRing R]
  [IsLocalRing R] :
-- imply
  ZariskiCotangentSpace R = (maximalIdeal R).Cotangent :=
-- proof
  rfl

/--
[ZariskiTangentSpace.eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiCotangentSpace.lean)
-/
@[path]
public theorem eq_dual
  {R : Type u}
  [CommRing R]
  [IsLocalRing R] :
-- imply
  ZariskiTangentSpace R = Module.Dual (ResidueField R) (CotangentSpace R) :=
-- proof
  rfl


-- created on 2026-10-23
