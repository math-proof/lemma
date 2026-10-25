/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean -/

import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Def.GroupTheory.BurnsidePaqb.ClassSum.Part2
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

omit [Fintype G] in
theorem classRep_spec (l : ConjClasses G) : ConjClasses.mk (classRep l) = l :=
  Classical.choose_spec (ConjClasses.mk_surjective l)

open Classical in
/-- The carrier finset of a class is the conjugacy class of its representative. -/
theorem carrier_toFinset (l : ConjClasses G) :
    (ConjClasses.carrier l).toFinset = conjClass (classRep l) := by
  rw [conjClass, Set.toFinset_inj, ConjAct.orbit_eq_carrier_conjClasses,
    classRep_spec l]

end BurnsidePaqb
