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
import Def.Combinatorics.DensityHalesJewett.Part6
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

@[simp]
theorem dhj_mem_support {ι : Type*} [Fintype ι] (x : ι → Fin 2) (i : ι) :
    i ∈ dhjSupport x ↔ x i = 1 := by
  simp [dhjSupport]

theorem dhjSupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (dhjSupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  have hi : x i = 1 ↔ y i = 1 := by
    simpa only [dhj_mem_support] using Finset.ext_iff.mp hxy i
  apply Fin.ext
  omega

end MathlibExt.Combinatorics.DensityHalesJewettWanted
