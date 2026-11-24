module
public import Theorem.GameTheory.ShapleyValue.Part3
public import Theorem.Set.ShapleyValue
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BondarevaShapley.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
/-! # Bondareva-Shapley theorem -/
section

namespace MathlibExt.GameTheory.BondarevaShapleyWanted

open Finset

open MathlibExt.GameTheory.ShapleyValue

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Core allocation: efficiency and coalitional rationality. -/
def IsCoreAllocation (v : CoopGame Player) (x : Player → ℝ) : Prop :=
  (∑ i : Player, x i = v.charFun Set.univ) ∧
    ∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i

/-- Balanced game via Bondareva-Shapley weights. -/
def IsBalanced (v : CoopGame Player) : Prop :=
  ∀ lam : Finset Player → ℝ,
    (∀ S, 0 ≤ lam S) →
    (∀ i : Player, ∑ S ∈ (Finset.univ.filter fun S => i ∈ S), lam S = 1) →
    ∑ S : Finset Player, lam S * v.charFun (S : Set Player) ≤ v.charFun Set.univ

end MathlibExt.GameTheory.BondarevaShapleyWanted
end
