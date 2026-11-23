/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/SphericalFiniteDiameter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.Building.Spherical
public import Theorem.Finset.AreOpposite.of.AreOpposite
public import Theorem.List.Any.of.Not.In_A.IsChainA
public import Theorem.Finset.OppositeSides.of.EqToSimplicialComplex.AreOppositeToSimplicialComplexToChamberComplex.IsMaximal.IsMaximal.In_Faces.In_Faces.In_Apartments.OppositeChamberHyp
public import Def.v1.Atlas.Buildings.code.Building.Convexity
public import Structure.v1.Atlas.Buildings.code.Building.OppositeChambers
public import Theorem.Finset.Adjacent.of.Adjacent
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Data.Set.Finite.List

@[expose] public section

variable {V : Type*} [DecidableEq V]


/-- A simplicial complex has *finite diameter* bounded by $d$ if every pair
of chambers has gallery distance at most $d$. -/
def SimplicialComplex.HasFiniteDiameter (K : SimplicialComplex V) (d : ℕ) : Prop :=
  ∀ C D, K.IsMaximal C → K.IsMaximal D → galleryDist K C D ≤ d

/-- A building has *finite diameter* if its underlying chamber complex does. -/
def Building.HasFiniteDiameter (b : Building V) (d : ℕ) : Prop :=
  b.toChamberComplex.toSimplicialComplex.HasFiniteDiameter d

