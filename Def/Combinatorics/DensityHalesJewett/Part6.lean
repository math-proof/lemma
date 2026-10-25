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
import Theorem.Combinatorics.DensityHalesJewett.Part4
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

def dhjLineTopEquiv {k : ℕ} {ι : Type*} :
    Combinatorics.Line (Fin k) ι ≃ {x : ι → Fin (k + 1) // dhjHasLast x} where
  toFun l := ⟨dhjLineTop l, dhjLineTop_hasLast l⟩
  invFun x := dhjLineOfTop x x.2
  left_inv := dhjLineOfTop_lineTop
  right_inv x := by
    apply Subtype.ext
    exact dhjLineTop_lineOfTop x.1 x.2

def dhjNoLastEquiv {k : ℕ} {ι : Type*} :
    {x : ι → Fin (k + 1) // ∀ i, x i ≠ Fin.last k} ≃ (ι → Fin k) where
  toFun x i := (x.1 i).castPred (x.2 i)
  invFun x := ⟨Fin.castSucc ∘ x, fun i => Fin.castSucc_ne_last _⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.castSucc_castPred _ _
  right_inv x := by
    funext i
    exact Fin.castPred_castSucc _

def dhjAt (k n : ℕ) (δ : ℝ) : Prop :=
  ∀ A : Finset (Fin n → Fin k), δ ≤ dhjDensity A →
    ∃ l : Combinatorics.Line (Fin k) (Fin n), dhjLineIn A l

def dhjThreshold (k : ℕ) (δ : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, dhjAt k n δ

noncomputable def dhjPullback {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) : Finset (η → α) := by
  classical
  exact Finset.univ.filter fun x => V x ∈ A

noncomputable def dhjDensityOn {η α ι : Type*}
    [Fintype η] [Fintype α] [Fintype (η → α)]
    (A : Finset (ι → α)) (V : Combinatorics.Subspace η α ι) : ℝ :=
  dhjDensity (dhjPullback V A)

def dhjSubspaceIn {η α ι : Type*} (A : Finset (ι → α))
    (V : Combinatorics.Subspace η α ι) : Prop := ∀ x, V x ∈ A

def dhjSupport {ι : Type*} [Fintype ι] (x : ι → Fin 2) : Finset ι :=
  Finset.univ.filter fun i => x i = 1

end MathlibExt.Combinatorics.DensityHalesJewettWanted
