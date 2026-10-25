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
import Def.Combinatorics.DensityHalesJewett.Part5
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

@[simp]
theorem dhjLineTop_lineOfTop {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1))
    (hx : dhjHasLast x) : dhjLineTop (dhjLineOfTop x hx) = x := by
  funext i
  generalize hxi : x i = a
  cases a using Fin.lastCases <;>
    simp [dhjLineTop, dhjLiftLine, dhjLineOfTop, Combinatorics.Line.coe_apply, hxi]

@[simp]
theorem dhjLineOfTop_lineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) :
    dhjLineOfTop (dhjLineTop l) (dhjLineTop_hasLast l) = l := by
  apply Combinatorics.Line.ext
  funext i
  cases hi : l.idxFun i <;>
    simp [dhjLineOfTop, dhjLineTop, dhjLiftLine, Combinatorics.Line.coe_apply, hi]

end MathlibExt.Combinatorics.DensityHalesJewettWanted
