import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.Cor2328
open GroupCohomology
open CategoryTheory


namespace GroupCohomology

/--
[corollary_23_28_homology_ind_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean)
-/
@[path]
lemma corollary_23_28_homology_ind_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [DecidableEq G]
  [Fintype G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) :=
-- proof
  homology_induced_vanishing A n

end GroupCohomology

namespace GroupCohomology

/--
[corollary_23_28_cohomology_coind_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean)
-/
@[path]
lemma corollary_23_28_cohomology_coind_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) :=
-- proof
  cohomology_coinduced_vanishing A n

end GroupCohomology

namespace GroupCohomology

/--
[corollary_23_28_cohomology_ind_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean)
-/
@[path]
lemma corollary_23_28_cohomology_ind_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
-- proof
  classical
  exact (cohomology_coinduced_vanishing A n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (lemma_23_27 A))

end GroupCohomology

namespace GroupCohomology

/--
[corollary_23_28_homology_coind_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean)
-/
@[path]
lemma corollary_23_28_homology_coind_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [DecidableEq G]
  [Fintype G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
-- proof
  classical
  exact (homology_induced_vanishing A n).of_iso
    ((groupHomology.functor k G (n + 1)).mapIso (lemma_23_27 A).symm)

end GroupCohomology

namespace GroupCohomology

/--
[induced_coinduced_cohomology_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean)
-/
@[path]
lemma induced_coinduced_cohomology_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)} :
-- imply
  Nonempty (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅ groupHomology A 0) ∧ Nonempty (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅ groupCohomology A 0) ∧ Nonempty (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅ groupHomology A 0) ∧ Nonempty (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅ groupCohomology A 0) ∧ (∀ n : ℕ, Limits.IsZero (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧ (∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧ (∀ n : ℕ, Limits.IsZero (groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) ∧ (∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1))) := by
-- proof
  classical
  exact ⟨⟨corollary_23_28_homology_ind_H0_iso A⟩,
    ⟨corollary_23_28_cohomology_ind_H0_iso A⟩,
    ⟨corollary_23_28_homology_coind_H0_iso A⟩,
    ⟨corollary_23_28_cohomology_coind_H0_iso A⟩,
    corollary_23_28_homology_ind_vanishing A,
    corollary_23_28_cohomology_ind_vanishing A,
    corollary_23_28_homology_coind_vanishing A,
    corollary_23_28_cohomology_coind_vanishing A⟩

end GroupCohomology


-- created on 2026-10-23
