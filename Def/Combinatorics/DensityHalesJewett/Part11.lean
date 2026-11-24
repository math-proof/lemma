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
public import Theorem.Combinatorics.DensityHalesJewett.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/
namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjFlattenEquiv {L G : ℕ} {α : Type*} :
    (Fin L → Fin G → α) ≃ (Fin L × Fin G → α) where
  toFun := dhjFlattenBlocks
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def dhjTheta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ / (4 * dhjLineCount k m₀)

noncomputable def dhjEta (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjTheta k m₀ δ / 48

noncomputable def dhjGamma (k m₀ : ℕ) (δ : ℝ) : ℝ :=
  δ * dhjEta k m₀ δ ^ 2 / k

end MathlibExt.Combinatorics.DensityHalesJewettWanted
