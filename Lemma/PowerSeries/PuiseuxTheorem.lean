import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.PuiseuxTheorem
open Polynomial
open HahnSeries
open MetaMathlibExt


/--
[isAlgClosed_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma isAlgClosed_rat_eq
  [Field K] [IsAlgClosed K] [CharZero K] :
-- imply
  IsAlgClosed (HahnSeries Rat K) := by
-- proof
  apply HahnSeries.isAlgClosed_rat

/--
[puiseux_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean)
-/
@[path]
private lemma puiseux_theorem_eq
  [Field K] [IsAlgClosed K] [CharZero K] :
-- imply
  IsAlgClosed (HahnSeries Rat K) ∧
    (∃ (ι : LaurentSeries K →+* HahnSeries Rat K)
    (P : Subfield (HahnSeries Rat K))
    (hmem : ∀ y, ι y ∈ P)
    (e : ↥P ≃+* AlgebraicClosure (LaurentSeries K)),
    Function.Injective ι ∧
    (∀ x : ↥P, ∃ n : ℕ, 0 < n ∧
    ∀ r : Rat, HahnSeries.coeff (x : HahnSeries Rat K) r ≠ 0 →
    ∃ m : ℤ, r = (m : Rat) / (n : Rat)) ∧
    (∀ y : HahnSeries Rat K,
    (∃ n : ℕ, 0 < n ∧
    ∀ r : Rat, HahnSeries.coeff y r ≠ 0 →
    ∃ m : ℤ, r = (m : Rat) / (n : Rat)) → y ∈ P) ∧
    (∀ y, e ⟨ι y, hmem y⟩ =
    algebraMap (LaurentSeries K)
    (AlgebraicClosure (LaurentSeries K)) y)) ∧
    Nonempty (LaurentSeries K ≃+* FractionRing (PowerSeries K)) := by
-- proof
  apply MetaMathlibExt.puiseux_theorem


-- created on 2026-10-20
