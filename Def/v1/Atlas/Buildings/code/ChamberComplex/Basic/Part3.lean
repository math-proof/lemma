/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Structure.v1.Atlas.Buildings.code.ChamberComplex.Basic.Part3
variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- `K` is *thin* if every codim-$1$ face $F$ of a chamber $C$ lies in exactly one other
chamber. -/
def IsThin (K : ChamberComplex V) : Prop :=
  ∀ F C, K.toSimplicialComplex.IsFacet F C → K.toSimplicialComplex.IsMaximal C →
    ∃! D, D ≠ C ∧ K.toSimplicialComplex.IsFacet F D ∧ K.toSimplicialComplex.IsMaximal D

/-- `K` is *thick* if every codim-$1$ face $F$ of a chamber $C$ lies in at least two
chambers distinct from $C$. -/
def IsThick (K : ChamberComplex V) : Prop :=
  ∀ F C, K.toSimplicialComplex.IsFacet F C → K.toSimplicialComplex.IsMaximal C →
    ∃ D₁ D₂, D₁ ≠ C ∧ D₂ ≠ C ∧ D₁ ≠ D₂ ∧
      K.toSimplicialComplex.IsFacet F D₁ ∧ K.toSimplicialComplex.IsMaximal D₁ ∧
      K.toSimplicialComplex.IsFacet F D₂ ∧ K.toSimplicialComplex.IsMaximal D₂

end ChamberComplex

/-- The combinatorial gallery distance $d(C,D)$ between chambers: $0$ if $C = D$, else the
infimum length over all galleries connecting $C$ and $D$. -/
noncomputable def galleryDist (K : SimplicialComplex V) (C D : Finset V) : ℕ :=
  if C = D then 0
  else sInf {n | ∃ g : Gallery K, g.Connects C D ∧ g.length = n}

