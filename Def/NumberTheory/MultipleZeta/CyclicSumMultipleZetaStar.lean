/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumMultipleZetaStar.lean -/

/- Authors: Adam Kiezun, Muse Spark 1.3 -/

import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
import Mathlib.Data.List.Rotate
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped ENNReal

open Topology


section

open scoped BigOperators

namespace MetaMathlibExt

namespace StarCyclic

/-- Nested finite sums over weakly decreasing chains; bottom weight `w`. -/
noncomputable def tailWS : List ℕ → (ℕ → ENNReal) → ℕ → ENNReal
  | [], w, A => w A
  | e :: t, w, A => ∑ y ∈ Finset.Icc 1 A, ((y : ENNReal) ^ e)⁻¹ * tailWS t w y

/-- Top-level sum over the largest variable (weak chains). -/
noncomputable def topSumS (e : ℕ) (t : List ℕ) (w : ℕ → ℕ → ENNReal) : ENNReal :=
  ∑' x : ℕ, if 0 < x then ((x : ENNReal) ^ e)⁻¹ * tailWS t (w x) x else 0

/-- ENNReal multiple zeta-star value in recursive form. -/
noncomputable def zetaRS : List ℕ → ENNReal
  | [] => 1
  | e :: t => topSumS e t (fun _ _ => 1)

/-- Harmonic bottom weight for `B` (weak chains, diagonal excluded). -/
noncomputable def harmStar (x y : ℕ) : ENNReal :=
  ∑ c ∈ Finset.Icc 1 y, (if c < x then (((x - c : ℕ) : ENNReal))⁻¹ else 0)

/-- Remainder weight for `A` (weak chains, diagonal excluded). -/
noncomputable def wWeightS (L x y : ℕ) : ENNReal :=
  ∑ c ∈ Finset.Icc 1 y,
    (if c < x then (x : ENNReal)⁻¹ * ((c : ENNReal) ^ (L - 1))⁻¹ *
      (((x - c : ℕ) : ENNReal))⁻¹ else 0)

/-- Auxiliary series `B`. -/
noncomputable def cycB : List ℕ → ENNReal
  | [] => 0
  | e :: t => topSumS e t harmStar

/-- ENNReal multiple zeta-star value in tuple form. -/
noncomputable def zetaEStar (l : List ℕ) : ENNReal :=
  ∑' n : Fin l.length → ℕ,
    if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((n a : ENNReal) ^ l.get a)⁻¹
    else 0

/-- Strict harmonic tail weight (for the telescoping lemma only). -/
noncomputable def harmTailLt (x y : ℕ) : ENNReal :=
  ∑ c ∈ Finset.range y, (((x - c : ℕ) : ENNReal))⁻¹

/-- Bundle a positive list as a multiple-zeta index. -/
noncomputable def toIndexS (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) :
    MultipleZeta.Index :=
  ⟨l.sum, ⟨l, fun {x} hx => hpos x hx, rfl⟩⟩

/-- Real harmonic numbers. -/
noncomputable def hR (x : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 x, ((m : ℝ))⁻¹

/-- ENNReal harmonic numbers. -/
noncomputable def Hstar (x : ℕ) : ENNReal :=
  ∑ m ∈ Finset.Icc 1 x, ((m : ENNReal))⁻¹

noncomputable def eps (p : ℕ) : ℝ := 1 / (2 * (p : ℝ) + 2)

noncomputable def capC (p : ℕ) : ℝ := 1 + 1 / eps p

end StarCyclic
end MetaMathlibExt
end
