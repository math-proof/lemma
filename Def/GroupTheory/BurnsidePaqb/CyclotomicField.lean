/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Galois.Basic
/-!
Cyclotomic-field stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/GaloisField.lean`.
-/


namespace BurnsidePaqb

open Polynomial

open Classical in
/-- The cyclotomic subfield of `ℂ`: `ℚ` adjoin the `m`-th roots of unity. -/
noncomputable def cycSubfield (m : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ↑(Polynomial.nthRootsFinset m (1 : ℂ))

end BurnsidePaqb
