/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CharacterOrthogonality.lean -/

import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Complex.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Abbrev.GroupTheory.BurnsidePaqb.CharacterOrthogonality
open CategoryTheory

/-!
Character-orthogonality stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ColumnOrth.lean`.
-/


namespace BurnsidePaqb

variable (G : Type) [Group G] [Fintype G]

open Classical in
/-- The delta class function at the identity. -/
noncomputable def deltaOne : G → ℂ := fun g => if g = 1 then 1 else 0

end BurnsidePaqb
