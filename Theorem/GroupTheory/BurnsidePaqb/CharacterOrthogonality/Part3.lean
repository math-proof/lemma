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
import Def.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part2
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

omit [Fintype G] in
theorem Irr.mk_repBundle (c : Irr G) : Quotient.mk _ (Irr.repBundle G c) = c :=
  Quotient.out_eq c

omit [Fintype G] in
theorem Irr.charFun_repBundle (c : Irr G) :
    (Irr.repBundle G c).1.character = Irr.charFun G c := by
  have h := Irr.charFun_mk G (Irr.repBundle G c)
  rw [Irr.mk_repBundle] at h
  exact h.symm

end BurnsidePaqb
