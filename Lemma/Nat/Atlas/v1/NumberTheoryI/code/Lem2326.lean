import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Lem2326
open GroupCohomology
open CategoryTheory


namespace GroupCohomology

/--
[homology_induced_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2326.lean)
-/
@[path]
lemma homology_induced_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [DecidableEq G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
-- proof
  haveI : Subsingleton ↥(⊥ : Subgroup G) := Unique.instSubsingleton
  exact (isZero_groupHomology_succ_of_subsingleton A n).of_iso
    (groupHomology.indIso (⊥ : Subgroup G) A (n + 1))

end GroupCohomology


-- created on 2026-10-23
