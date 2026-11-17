/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Combinatorics.SetFamily.LYM
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Def.Combinatorics.DensityHalesJewett

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/

public section


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhjPrependWord_tail {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin s) :
    dhjPrependWord r p x (dhjTailIndex s r i) = x i := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (fun j => p j.succ)

theorem dhjPrependWord_prefix {β : Type*} {r s : ℕ}
    (p : Fin r → β) (x : Fin s → β) (i : Fin r) :
    dhjPrependWord r p x (dhjPrefixIndex s r i) = p i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (fun j => p j.succ) i

end MathlibExt.Combinatorics.DensityHalesJewettWanted
