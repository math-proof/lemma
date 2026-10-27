import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.DimensionCotangentRegularity
open KaehlerDifferential Algebra IsLocalRing Module
open scoped TensorProduct


/--
[goal135_leibniz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean)
-/
@[path]
lemma goal135_leibniz
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  {a b : A} :
-- imply
  KaehlerDifferential.D k A (a * b) = a • KaehlerDifferential.D k A b + b • KaehlerDifferential.D k A a :=
-- proof
  (KaehlerDifferential.D k A).leibniz a b

/--
[goal135_map_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean)
-/
@[path]
lemma goal135_map_algebraMap
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  {r : k} :
-- imply
  KaehlerDifferential.D k A (algebraMap k A r) = 0 :=
-- proof
  (KaehlerDifferential.D k A).map_algebraMap r

/--
[goal135_span_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean)
-/
@[path]
lemma goal135_span_range
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A] :
-- imply
  Submodule.span A (Set.range (KaehlerDifferential.D k A)) = ⊤ :=
-- proof
  KaehlerDifferential.span_range_derivation k A
section Goal136
variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/--
[goal136_lift_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean)
-/
@[path]
lemma goal136_lift_comp
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  [AddCommGroup M]
  [Module k M]
  [Module A M]
  [IsScalarTower k A M]
  {D' : Derivation k A M} :
-- imply
  D'.liftKaehlerDifferential.compDer (KaehlerDifferential.D k A) = D' :=
-- proof
  Derivation.liftKaehlerDifferential_comp D'

/--
[goal136_lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean)
-/
@[path]
lemma goal136_lift_unique
  {k : Type u}
  {A : Type v}
  [CommRing k]
  [CommRing A]
  [Algebra k A]
  [AddCommGroup M]
  [Module k M]
  [Module A M]
  [IsScalarTower k A M]
  {f g : Ω[A⁄k] →ₗ[A] M}
-- given
  (hfg : f.compDer (KaehlerDifferential.D k A) = g.compDer (KaehlerDifferential.D k A)) :
-- imply
  f = g :=
-- proof
  Derivation.liftKaehlerDifferential_unique f g hfg
end Goal136


-- created on 2026-10-23
