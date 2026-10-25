/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Uniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace SimplicialComplex

/-- A simplicial morphism $K \to L$: a vertex map sending each face of $K$ to a face of $L$. -/
structure Morphism (K : SimplicialComplex V) (L : SimplicialComplex W) where
  toFun : V → W
  map_face : ∀ s ∈ K.faces, s.image toFun ∈ L.faces

end SimplicialComplex
