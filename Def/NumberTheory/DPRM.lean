/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Computability.RE
import Mathlib.NumberTheory.Dioph
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic
import Inductive.NumberTheory.DPRM
open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- Modulus for the product trick: `N = t * (1 + x * t) ^ x + 1`. -/
def dpProdN (x t : ℕ) : ℕ := t * (1 + x * t) ^ x + 1

/-- The product `Π_{j<x} (1 + (j+1) * t)`. -/
def dpProdP (x t : ℕ) : ℕ :=
  ∏ j ∈ Finset.range x, (1 + (j + 1) * t)

end MathlibExt.NumberTheory.DPRMWanted
