/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/RetractionDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Retraction
variable {V : Type*} [DecidableEq V]


/-- A retraction $\rho_{D;C,A} : X \to A$ of a building $X$ onto an apartment
$A$ centered at a chamber $C$ (the `base`): a simplicial map fixing $A$
pointwise, sending each chamber of $X$ to a chamber of $A$, and preserving
adjacency up to collapse. -/
structure BuildingRetraction (b : Building V) where
  apt : SimplicialComplex V
  apt_mem : apt ∈ b.apartmentSystem.apartments
  base : Finset V
  base_maximal : apt.IsMaximal base
  map : V → V
  map_face : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s.image map ∈ apt.faces
  map_fixes : ∀ v, (∃ s ∈ apt.faces, v ∈ s) → map v = v
  map_chamber : ∀ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C →
    apt.IsMaximal (C.image map)
  map_adj_or_eq : ∀ C D,
    b.toChamberComplex.toSimplicialComplex.Adjacent C D →
    C.image map = D.image map ∨ apt.Adjacent (C.image map) (D.image map)

