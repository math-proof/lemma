/-
Copyright (c) 2026 Mathlib Extension Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.AffineSpace
import Class.AlgebraicGeometry.Variety
universe u

open CategoryTheory Limits

/-!
# Varieties over a field

A *variety* over a field `k` is a scheme `X` equipped with a structure morphism to
`Spec k` that is separated, of finite type, and geometrically reduced.

We follow the "geometric" convention (see Görtz–Wedhorn, *Algebraic Geometry I*, and the
Stacks project morphism-property tags): the structure morphism `X ⟶ Spec k` is
* separated (`AlgebraicGeometry.IsSeparated`, Stacks tag `01KM`),
* of finite type, i.e. quasi-compact and locally of finite type
  (`AlgebraicGeometry.QuasiCompact` + `AlgebraicGeometry.LocallyOfFiniteType`, Stacks tag `01T0`),
* geometrically reduced (`AlgebraicGeometry.GeometricallyReduced`, Stacks tag `0364`).

Requiring geometric (rather than plain) reducedness makes the notion stable under base
change / field extension, which is why it is the "geometric" convention.

## Main definitions

* `AlgebraicGeometry.IsVariety`: the predicate on a `k`-scheme of being a variety over `k`.

## Implementation notes

`IsVariety` is a `Prop`-valued `class` on `AlgebraicGeometry.Scheme` whose separatedness,
finite-type, and geometric-reducedness hypotheses are stated explicitly on the structure
morphism `X ↘ Spec (CommRingCat.of k)` (obtained from the `X.Over (Spec (CommRingCat.of k))`
instance). It is built by composing existing Mathlib morphism properties rather than
introducing any new primitive.
-/


namespace AlgebraicGeometry

variable (k : Type u) [Field k]

namespace IsVariety

variable {k}

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

instance [IsVariety k X] : IsSeparated (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.isSeparated

instance [IsVariety k X] : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.locallyOfFiniteType

instance [IsVariety k X] : QuasiCompact (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.quasiCompact

instance [IsVariety k X] : GeometricallyReduced (X ↘ Spec (CommRingCat.of k)) :=
  IsVariety.geometricallyReduced

end IsVariety
end AlgebraicGeometry
