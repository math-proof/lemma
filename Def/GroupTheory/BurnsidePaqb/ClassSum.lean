/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean -/

module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Complex.Basic
public import Theorem.GroupTheory.BurnsidePaqbReduction.Part2

@[expose] public section

/-!
Conjugacy-class-algebra stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is the conjugacy-class-algebra stage of the complete Burnside proof,
mechanically ported from the audited source `extracted/Burnside/ClassSum.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

/-- The class sum of a finset: sum of the group elements in the group algebra. -/
noncomputable def classSum (C : Finset G) : MonoidAlgebra ℂ G :=
  ∑ x ∈ C, MonoidAlgebra.of ℂ G x

end BurnsidePaqb
