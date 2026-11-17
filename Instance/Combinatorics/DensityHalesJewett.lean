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
public import Def.Combinatorics.DensityHalesJewett.Part2
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/

@[expose] public section

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

noncomputable instance dhjFiniteLine {α ι : Type*} [Finite α] [Finite ι] :
    Finite (Combinatorics.Line α ι) :=
  Finite.of_injective Combinatorics.Line.idxFun fun _ _ h => Combinatorics.Line.ext h

noncomputable instance dhjFintypeLine {α ι : Type*} [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Line α ι) := Fintype.ofFinite _

noncomputable instance dhjFiniteSubspace {η α ι : Type*}
    [Finite η] [Finite α] [Finite ι] :
    Finite (Combinatorics.Subspace η α ι) :=
  Finite.of_injective Combinatorics.Subspace.idxFun fun _ _ h =>
    Combinatorics.Subspace.ext h

noncomputable instance dhjFintypeSubspace {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype ι] :
    Fintype (Combinatorics.Subspace η α ι) := Fintype.ofFinite _

end MathlibExt.Combinatorics.DensityHalesJewettWanted
