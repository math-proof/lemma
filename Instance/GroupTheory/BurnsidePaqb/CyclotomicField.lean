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
import Theorem.GroupTheory.BurnsidePaqb.CyclotomicField
/-!
Cyclotomic-field stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/GaloisField.lean`.
-/


namespace BurnsidePaqb

open Polynomial

instance cyc_finiteDimensional (m : ℕ) : FiniteDimensional ℚ (cycSubfield m) := by
  classical
  by_cases hm : m = 0
  · subst hm
    rw [cycSubfield_zero]
    infer_instance
  · have hsplit := cyc_isSplitting m hm
    exact @IsSplittingField.finiteDimensional ℚ _ _ _ _ (X ^ m - C 1 : ℚ[X]) hsplit

instance cyc_isGalois (m : ℕ) : IsGalois ℚ (cycSubfield m) := by
  classical
  by_cases hm : m = 0
  · subst hm
    rw [cycSubfield_zero]
    exact (IntermediateField.botEquiv ℚ ℂ).transfer_galois.mpr (IsGalois.self ℚ)
  · have hsplit := cyc_isSplitting m hm
    have hsep : (X ^ m - C 1 : ℚ[X]).Separable :=
      separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hm) one_ne_zero
    exact @IsGalois.of_separable_splitting_field ℚ _ _ _ _ (X ^ m - C 1 : ℚ[X])
      hsplit hsep

end BurnsidePaqb
