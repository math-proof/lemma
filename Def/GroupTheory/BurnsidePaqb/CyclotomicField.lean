/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CyclotomicField.lean -/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

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
