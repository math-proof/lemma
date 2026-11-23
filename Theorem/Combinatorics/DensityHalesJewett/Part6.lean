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
public import Def.Combinatorics.DensityHalesJewett.Part7

@[expose] public section

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

@[simp]
theorem dhjLineOfSupport_zero {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 0 = x := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have hx : x i ≠ 1 := by
      intro hx
      have hy := hsub (dhj_mem_support x i |>.mpr hx)
      exact hi (hx.trans (dhj_mem_support y i |>.mp hy).symm)
    have hx0 : x i = 0 := by
      apply Fin.ext
      omega
    have hne : (0 : Fin 2) ≠ y i := by
      intro h
      exact hi (hx0.trans h)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hx0, hne]

@[simp]
theorem dhjLineOfSupport_one {ι : Type*} [Fintype ι] (x y : ι → Fin 2)
    (hxy : dhjSupport x ⊂ dhjSupport y) : dhjLineOfSupport x y hxy 1 = y := by
  funext i
  by_cases hi : x i = y i
  · simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hi]
  · have hsub := hxy.1
    have himp : x i = 1 → y i = 1 := by
      intro hx
      exact dhj_mem_support y i |>.mp (hsub (dhj_mem_support x i |>.mpr hx))
    have hy : y i = 1 := by
      apply Fin.ext
      omega
    have hx : x i ≠ 1 := by
      intro hx
      exact hi (hx.trans hy.symm)
    simp [dhjLineOfSupport, Combinatorics.Line.coe_apply, hy, hx]

end MathlibExt.Combinatorics.DensityHalesJewettWanted
