/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Theorem.Combinatorics.DensityHalesJewett.Part5
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
