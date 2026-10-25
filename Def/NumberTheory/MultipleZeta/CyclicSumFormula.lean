/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/CyclicSumFormula.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Rotate
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.NumberTheory.MultipleZeta.Series.Part3
import Lemma.Nat.MultipleZeta.Series
import Lemma.Nat.MultipleZeta.Convergence
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
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

noncomputable def multipleZetaValue (k : List ℕ) : ℝ :=
  ∑' n : Fin k.length → ℕ,
    if (∀ a b : Fin k.length, a < b → n b < n a) ∧
        (∀ a : Fin k.length, 0 < n a) then
      ∏ a : Fin k.length, ((n a : ℝ) ^ k.get a)⁻¹
    else 0

namespace CyclicSumFormula

/-- Bundle a positive list as a multiple-zeta index. -/
noncomputable def toIndex (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) :
    MultipleZeta.Index :=
  ⟨l.sum, ⟨l, fun {x} hx => hpos x hx, rfl⟩⟩

/-- The left-hand index of the cyclic sum formula, bundled as a
`MultipleZeta.Index`. Off the summation range it defaults to `[2]`. -/
noncomputable def leftIndex (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) (i : ℕ) : MultipleZeta.Index :=
  if hmem : i ∈ Finset.Icc 1 (k.get j - 1) then
    toIndex ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) (by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hmem).1
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
          rw [List.mem_rotate] at hxR
          have h1 := hk_pos x hxR
          omega
        · rw [List.mem_singleton] at hx
          omega)
  else
    toIndex [2] (fun x hx => by rw [List.mem_singleton] at hx; omega)

/-- The right-hand index of the cyclic sum formula, bundled as a
`MultipleZeta.Index`. -/
noncomputable def rightIndex (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) : MultipleZeta.Index :=
  toIndex ((k.get j + 1) :: (k.rotate j.1).tail) (by
    intro x hx
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
      rw [List.mem_rotate] at hxR
      have h1 := hk_pos x hxR
      omega)

-- D1: nested finite sums over decreasing chains; bottom weight `w` at the chain bottom
-- (or at `A` itself when the list is empty).
noncomputable def tailW : List ℕ → (ℕ → ℝ≥0∞) → ℕ → ℝ≥0∞
  | [], w, A => w A
  | e :: t, w, A => ∑ y ∈ Finset.Ioo 0 A, ((y : ℝ≥0∞) ^ e)⁻¹ * tailW t w y

-- D2: top-level sum over the largest variable.
noncomputable def topSum (e : ℕ) (t : List ℕ) (w : ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : ℕ, if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailW t (w x) x else 0

-- D3: ENNReal multiple zeta value in recursive form.
noncomputable def zetaR : List ℕ → ℝ≥0∞
  | [] => 1
  | e :: t => topSum e t (fun _ _ => 1)

-- D4: harmonic tail weight.
noncomputable def harmTail (x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.range y, (((x - c : ℕ) : ℝ≥0∞))⁻¹

-- D5: auxiliary series T.
noncomputable def cycT : List ℕ → ℝ≥0∞
  | [] => 0
  | e :: t => topSum e t harmTail

-- D6: remainder weight after splitting off the top variable.
noncomputable def wWeight (L x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.Ioo 0 y, (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹

-- D7: ENNReal multiple zeta value in tuple form (Wanted summand with ℝ≥0∞).
noncomputable def zetaE (l : List ℕ) : ℝ≥0∞ :=
  ∑' n : Fin l.length → ℕ,
    if (∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹
    else 0

end CyclicSumFormula
end MetaMathlibExt
end
