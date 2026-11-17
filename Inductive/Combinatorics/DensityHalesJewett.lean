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
public import Def.Combinatorics.DensityHalesJewett.Part3
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

public inductive dhjTiled (d k : ℕ) {ι : Type*}
    [DecidableEq (ι → Fin (k + 1))] :
    Finset (ι → Fin (k + 1)) → Prop
  | empty : dhjTiled d k ∅
  | add (C : Finset (ι → Fin (k + 1)))
      (V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) ι) :
      dhjTiled d k C → Disjoint C (dhjSubspacePoints V) →
        dhjTiled d k (C ∪ dhjSubspacePoints V)

end MathlibExt.Combinatorics.DensityHalesJewettWanted
