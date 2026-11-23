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
public import Theorem.Combinatorics.DensityHalesJewett.Part6

@[expose] public section

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ¬dhjLineIn A l

end MathlibExt.Combinatorics.DensityHalesJewettWanted
