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
import Theorem.GroupTheory.BurnsidePaqb.CharacterOrthogonality.Part5
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
/-- Iso-classes form a finite type. -/
noncomputable instance [Finite G] : Finite (Irr G) := by
  let _ : Fintype G := Fintype.ofFinite G
  rw [← not_infinite_iff_finite]
  intro hInf
  have e := Infinite.natEmbedding (Irr G)
  set N := Fintype.card G
  have hcard := cardBound G (Finset.map e (Finset.range (N + 1)))
  rw [Finset.card_map, Finset.card_range] at hcard
  omega

noncomputable instance : Fintype (Irr G) := Fintype.ofFinite _

end BurnsidePaqb
