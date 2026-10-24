/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec22BertiniProper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic

section BertiniPredicates

variable (k : Type*) [Field k]
variable (V : Type*) [AddCommGroup V] [Module k V]

/-- Opaque predicate asserting that a subset of `ℙ(V)` is a smooth (closed) subvariety. -/
opaque IsSmoothSubvariety : Set (Projectivization k V) → Prop

/-- The hyperplane in `ℙ(V)` cut out by a point `H ∈ ℙ(V*)`, namely the zero locus of a
representative linear form. -/
noncomputable def projectiveHyperplane :
    Projectivization k (Module.Dual k V) → Set (Projectivization k V) :=
  fun H => {p : Projectivization k V | (Projectivization.rep H) (Projectivization.rep p) = 0}

/-- Opaque predicate asserting that a subset of the dual projective space `ℙ(V*)`
is a nonempty Zariski-open subset. -/
opaque IsNonemptyZariskiOpen :
  Set (Projectivization k (Module.Dual k V)) → Prop

/-- Opaque predicate asserting that a subset of the dual projective space `ℙ(V*)`
is a proper Zariski-closed subset (i.e., closed and not the whole space). -/
opaque IsProperZariskiClosed :
  Set (Projectivization k (Module.Dual k V)) → Prop

end BertiniPredicates

/-- Bertini "bad locus" lemma: For a smooth projective subvariety `X`, the set of
hyperplanes `H` for which `X ∩ H` is not smooth is contained in a proper closed subset
of the dual projective space. -/
