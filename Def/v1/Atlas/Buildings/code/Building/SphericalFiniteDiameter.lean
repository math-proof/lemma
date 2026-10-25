/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/SphericalFiniteDiameter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Spherical
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.List.Any.of.Not.In_A.IsChainA
import Lemma.Finset.OppositeSides.of.EqToSimplicialComplex.AreOppositeToSimplicialComplexToChamberComplex.IsMaximal.IsMaximal.In_Faces.In_Faces.In_Apartments.OppositeChamberHyp
import Def.v1.Atlas.Buildings.code.Building.Convexity
import Structure.v1.Atlas.Buildings.code.Building.OppositeChambers
import Lemma.Finset.Adjacent.of.Adjacent
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.Set.Finite.List
variable {V : Type*} [DecidableEq V]


/-- A simplicial complex has *finite diameter* bounded by $d$ if every pair
of chambers has gallery distance at most $d$. -/
def SimplicialComplex.HasFiniteDiameter (K : SimplicialComplex V) (d : ℕ) : Prop :=
  ∀ C D, K.IsMaximal C → K.IsMaximal D → galleryDist K C D ≤ d

/-- A building has *finite diameter* if its underlying chamber complex does. -/
def Building.HasFiniteDiameter (b : Building V) (d : ℕ) : Prop :=
  b.toChamberComplex.toSimplicialComplex.HasFiniteDiameter d

