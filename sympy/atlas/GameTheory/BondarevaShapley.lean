/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BondarevaShapley.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import sympy.atlas.GameTheory.ShapleyValue
import Lemma.Set.ShapleyValue
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace MathlibExt.GameTheory.BondarevaShapleyWanted

/-! # Bondareva-Shapley theorem -/

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
