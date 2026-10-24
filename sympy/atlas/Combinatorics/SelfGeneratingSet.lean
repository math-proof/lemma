/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SelfGeneratingSet.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Lattice

namespace MetaMathlibExt
namespace SelfGeneratingSet

/-!
# Self-generating sets

This file formalizes the characterization of self-generating sets from Peter Hinz,
*On generalized Lichtenberg figures*, Journal of Integer Sequences 25 (2022), Article 22.6.5,
lines 163–180 of the source:

<https://cs.uwaterloo.ca/journals/JIS/VOL25/Hinz/hinz5.tex>

The archived source has SHA-256
`4c3205a109846590bbaf42330e44139bc52250e1712be01e11c7580312e7b134`.

Concept `jis_term_23e11a02338d8f3d91eda68b`; source statement
`jis_b9342f43164eb6b4d229b602`.
-/

/-- Every generator in `F` strictly increases its argument. -/
def StrictGrowth (F : Finset (Nat → Nat)) : Prop :=
  ∀ f ∈ F, ∀ x, x < f x

/-- `Gamma` contains `seed` and is closed under every generator in `F`. This is the source's
`SG(seed, F)` condition. -/
def SG (F : Finset (Nat → Nat)) (seed : Nat) (Gamma : Set Nat) : Prop :=
  seed ∈ Gamma ∧ ∀ f ∈ F, ∀ x ∈ Gamma, f x ∈ Gamma

/-- The fixed-point characterization of the self-generating set: each element is either the seed
or the image under a generator of an element already in the set. -/
def FixedPoint (F : Finset (Nat → Nat)) (seed : Nat) (C : Set Nat) : Prop :=
  ∀ y, y ∈ C ↔ y = seed ∨ ∃ f ∈ F, ∃ x ∈ C, f x = y

/-- Reachability from `seed` by a finite composition of generators in `F`. The constructor
`seed_mem` represents the empty composition. -/
inductive Gen (F : Finset (Nat → Nat)) (seed : Nat) : Nat → Prop where
  | seed_mem : Gen F seed seed
  | step (w : Nat) : Gen F seed w → ∀ f ∈ F, Gen F seed (f w)

/-- The closure of `seed` under finite compositions of generators in `F`. -/
def GeneratedSet (F : Finset (Nat → Nat)) (seed : Nat) : Set Nat :=
  {y | Gen F seed y}
end SelfGeneratingSet
end MetaMathlibExt
