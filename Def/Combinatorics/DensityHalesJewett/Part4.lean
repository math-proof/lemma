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
public import Inductive.Combinatorics.DensityHalesJewett

@[expose] public section

/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

noncomputable def dhjLineCount (k n : ℕ) : ℕ :=
  Nat.card (Combinatorics.Line (Fin k) (Fin n))

def dhjLiftLine {k : ℕ} {ι : Type*} (l : Combinatorics.Line (Fin k) ι) :
    Combinatorics.Line (Fin (k + 1)) ι where
  idxFun i := (l.idxFun i).map Fin.castSucc
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [hi]⟩

def dhjLineTop {k : ℕ} {ι : Type*}
    (l : Combinatorics.Line (Fin k) ι) : ι → Fin (k + 1) :=
  dhjLiftLine l (Fin.last k)

def dhjHasLast {k : ℕ} {ι : Type*} (x : ι → Fin (k + 1)) : Prop :=
  ¬∀ i, x i ≠ Fin.last k

end MathlibExt.Combinatorics.DensityHalesJewettWanted
