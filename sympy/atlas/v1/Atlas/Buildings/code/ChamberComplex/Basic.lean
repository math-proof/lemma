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

variable {V : Type*} [DecidableEq V]

/-- An abstract simplicial complex on a vertex set $V$: a downward-closed family of
nonempty finite subsets ("faces") of $V$. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  faces : Set (Finset V)
  nonempty_of_mem : ∀ s ∈ faces, s.Nonempty
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces

namespace SimplicialComplex

/-- `y` is a face of `x` in `K`: both are faces of $K$ and $y ⊆ x$. -/
def IsFace (K : SimplicialComplex V) (y x : Finset V) : Prop :=
  y ∈ K.faces ∧ x ∈ K.faces ∧ y ⊆ x

/-- `y` is a codimension-$1$ face ("facet") of `x` in `K`: $y$ is a face of $x$ with
$|x \setminus y| = 1$. -/
def IsFacet (K : SimplicialComplex V) (y x : Finset V) : Prop :=
  K.IsFace y x ∧ (x \ y).card = 1

/-- `x` is a maximal face ("chamber") of `K`: a face contained in no strictly larger face. -/
def IsMaximal (K : SimplicialComplex V) (x : Finset V) : Prop :=
  x ∈ K.faces ∧ ∀ y ∈ K.faces, x ⊆ y → x = y

/-- Two distinct chambers $C, D$ are adjacent if they share a common codim-$1$ facet $F$. -/
def Adjacent (K : SimplicialComplex V) (C D : Finset V) : Prop :=
  K.IsMaximal C ∧ K.IsMaximal D ∧ C ≠ D ∧ ∃ F, K.IsFacet F C ∧ K.IsFacet F D

end SimplicialComplex

/-- A gallery in `K`: a nonempty list of chambers in which consecutive entries are adjacent. -/
structure Gallery (K : SimplicialComplex V) where
  chambers : List (Finset V)
  length_pos : chambers.length > 0
  all_maximal : ∀ C ∈ chambers, K.IsMaximal C
  adjacent_consecutive : List.IsChain K.Adjacent chambers

/-- The combinatorial length of a gallery: number of edges = (number of chambers) $- 1$. -/
def Gallery.length {K : SimplicialComplex V} (g : Gallery K) : ℕ :=
  g.chambers.length - 1

/-- The gallery `g` "connects" $C$ to $D$ if its first chamber is $C$ and its last chamber is $D$. -/
def Gallery.Connects {K : SimplicialComplex V} (g : Gallery K) (C D : Finset V) : Prop :=
  g.chambers.head? = some C ∧ g.chambers.getLast? = some D

/-- A chamber complex: every face is contained in some chamber, and any two chambers are
connected by a gallery. -/
structure ChamberComplex (V : Type*) [DecidableEq V] extends SimplicialComplex V where
  exists_maximal : ∀ s ∈ faces, ∃ C, toSimplicialComplex.IsMaximal C ∧ s ⊆ C
  gallery_connected : ∀ C D, toSimplicialComplex.IsMaximal C →
    toSimplicialComplex.IsMaximal D → ∃ g : Gallery toSimplicialComplex,
    g.chambers.head? = some C ∧ g.chambers.getLast? = some D

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

/-- Self-distance is zero: $d(C,C) = 0$. -/
theorem galleryDist_self (K : SimplicialComplex V) (C : Finset V) :
    galleryDist K C C = 0 := by
  unfold galleryDist
  simp
