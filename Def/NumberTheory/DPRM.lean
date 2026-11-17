/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Computability.RE
public import Mathlib.NumberTheory.Dioph
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Logic.Godel.GodelBetaFunction
public import Mathlib.Tactic
public import Inductive.NumberTheory.DPRM

@[expose] public section

open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- Modulus for the product trick: `N = t * (1 + x * t) ^ x + 1`. -/
def dpProdN (x t : ℕ) : ℕ := t * (1 + x * t) ^ x + 1

/-- The product `Π_{j<x} (1 + (j+1) * t)`. -/
def dpProdP (x t : ℕ) : ℕ :=
  ∏ j ∈ Finset.range x, (1 + (j + 1) * t)

end MathlibExt.NumberTheory.DPRMWanted
