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
import Def.Combinatorics.DensityHalesJewett.Part3
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

inductive dhjTiled (d k : ℕ) {ι : Type*}
    [DecidableEq (ι → Fin (k + 1))] :
    Finset (ι → Fin (k + 1)) → Prop
  | empty : dhjTiled d k ∅
  | add (C : Finset (ι → Fin (k + 1)))
      (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) ι) :
      dhjTiled d k C → Disjoint C (dhjSubspacePoints V) →
        dhjTiled d k (C ∪ dhjSubspacePoints V)

end MathlibExt.Combinatorics.DensityHalesJewettWanted
