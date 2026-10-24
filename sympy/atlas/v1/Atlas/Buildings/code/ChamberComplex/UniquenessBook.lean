/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/UniquenessBook.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace ChamberComplex

/-- `f` *fixes $C$ pointwise*: $f(v) = v$ for every $v \in C$. -/
def FixesPointwise
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (C : Finset V) : Prop :=
  ∀ v ∈ C, f.toFun v = v

/-- The image of a gallery under $f$ *stutters*: some adjacent pair of chambers in the list has
equal $f$-images. -/
def ImageGalleryStutters
    {K : ChamberComplex V}
    (f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex)
    (cs : List (Finset V)) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < cs.length),
    (cs.get ⟨i, by omega⟩).image f.toFun =
    (cs.get ⟨i + 1, hi⟩).image f.toFun
