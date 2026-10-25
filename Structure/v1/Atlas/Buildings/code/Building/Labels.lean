/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Labels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
open scoped Classical

variable {V : Type*} [DecidableEq V]


/-- A labelling of a simplicial complex $K$ by a set $L$: a strict-monotone assignment of a finite,
nonempty set of labels to each face, monotone with respect to face inclusion. -/
structure Labelling (K : SimplicialComplex V) (L : Type*) [DecidableEq L] where
  labelMap : Finset V → Finset L
  label_nonempty : ∀ s ∈ K.faces, (labelMap s).Nonempty
  label_strictMono : ∀ s t, s ∈ K.faces → t ∈ K.faces →
    s ⊂ t → labelMap s ⊂ labelMap t

