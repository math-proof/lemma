import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false

open IsLocalRing

namespace IsLocalRing

class IsAdicTopology (R : Type*) [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Prop where
  isAdic : IsAdic (maximalIdeal R)

end IsLocalRing

class Algebra.TopologicallyFG (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] : Prop where
  out : ∃ s : Finset S, Dense (Algebra.adjoin R (s : Set S) : Set S)

instance (priority := 100) {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

open RingTheory in

noncomputable def Module.depth (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }

section PatchingPredicates

attribute [local instance] Module.quotientAnnihilator

variable {ι : Type*}

class Algebra.UniformlyBoundedRank (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsLocalRing (R i)] : Prop where
  cond : ∀ k, ∃ n : ℕ, ∀ i, Nat.card (R i ⧸ maximalIdeal (R i) ^ k) < n

class Module.UniformlyBoundedRank (R : Type*) (M : ι → Type*) [CommRing R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] : Prop where
  cond : ∃ n : ℕ, ∀ i, Module.rank (R ⧸ Module.annihilator R (M i)) (M i) < n

class IsPatchingSystem (R : Type*) (M : ι → Type*) [CommRing R] [TopologicalSpace R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (F : Filter ι) : Prop where
  cond : ∀ α : Ideal R, IsOpen (X := R) α → ∀ᶠ i in F, Module.annihilator R (M i) ≤ α

end PatchingPredicates
