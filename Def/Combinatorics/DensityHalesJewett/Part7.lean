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
public import Theorem.Combinatorics.DensityHalesJewett.Part5

@[expose] public section

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjLineOfSupport {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : Combinatorics.Line (Fin 2) ι where
  idxFun i := if x i = y i then some (x i) else none
  proper := by
    obtain ⟨i, hiy, hix⟩ := Finset.exists_of_ssubset hxy
    have hne : x i ≠ y i := by
      intro hi
      have hy : y i = 1 := dhj_mem_support y i |>.mp hiy
      exact hix (dhj_mem_support x i |>.mpr (hi.trans hy))
    exact ⟨i, by simp [hne]⟩

end MathlibExt.Combinatorics.DensityHalesJewettWanted
