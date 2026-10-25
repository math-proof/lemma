/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean -/

import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Theorem.GroupTheory.BurnsidePaqb.ClassSum.Part2
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

open Classical in
/-- Structure constant: number of pairs `(x, y) ∈ Ci × Cj` with `x * y = z`. -/
noncomputable def structConst (Ci Cj : Finset G) (z : G) : ℕ :=
  ((Ci.product Cj).filter (fun p => p.1 * p.2 = z)).card

end BurnsidePaqb
