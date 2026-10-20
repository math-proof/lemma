/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AmenableGroup.lean -/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.PUnit

open scoped Pointwise Classical symmDiff

/-! # Amenable groups via the Følner condition

A discrete group `G` is *amenable* when it satisfies the **Følner condition**: for
every finite subset `K ⊆ G` and every `ε > 0` there is a finite nonempty subset
`F ⊆ G` that is *almost invariant* under left translation by the elements of `K`,
i.e. `|s • F ∆ F| / |F| < ε` for every `s ∈ K`.

This is the measure-theory-free characterization of amenability. It is classically
equivalent to the existence of a finitely-additive left-invariant probability
measure (an invariant mean / Banach mean) on `G`; that equivalence is not proved
here. Mathlib's `Mathlib.MeasureTheory.Group.FoelnerFilter` develops a
*measure-theoretic* Følner filter for a group action `MulAction G X` on a measure
space and derives an invariant mean on `Set X` (`IsFoelner.amenable`), but it does
not provide this combinatorial predicate on a discrete group; hence the definition
below.

Reference: Følner, *On groups with full Banach mean value* (1955);
cf. Ceccherini-Silberstein–Coornaert, *Cellular Automata and Groups*, Ch. 4. -/

/-- A discrete group `G` is **amenable** if it satisfies the Følner condition: for
every finite set `K` and every `ε > 0` there is a finite nonempty set `F` with
`|s • F ∆ F| / |F| < ε` for all `s ∈ K`. -/
def IsAmenable (G : Type*) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ F : Finset G, F.Nonempty ∧
      ∀ s ∈ K, (((s • F) ∆ F).card : ℝ) / (F.card : ℝ) < ε

/-- Every finite group is amenable: the whole group `Finset.univ` is invariant under
left translation, so it is a Følner set with symmetric-difference ratio `0`. -/
theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] : IsAmenable G := by
  letI := Fintype.ofFinite G
  intro K ε hε
  refine ⟨Finset.univ, ⟨1, Finset.mem_univ 1⟩, fun s _ => ?_⟩
  rw [Finset.smul_finset_univ, symmDiff_self]
  simpa using hε

/-- Every trivial (subsingleton) group is amenable, witnessed by `F = {1}`. -/
theorem isAmenable_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    IsAmenable G := by
  intro K ε hε
  refine ⟨{1}, Finset.singleton_nonempty 1, fun s _ => ?_⟩
  rw [Finset.smul_finset_singleton, Subsingleton.elim (s • (1 : G)) 1, symmDiff_self]
  simpa using hε

/-- The symmetric group `S₃` is amenable (an ordinary finite example). -/
example : IsAmenable (Equiv.Perm (Fin 3)) := isAmenable_of_finite _

/-- The trivial group is amenable (a boundary example). -/
example : IsAmenable PUnit := isAmenable_of_subsingleton _
