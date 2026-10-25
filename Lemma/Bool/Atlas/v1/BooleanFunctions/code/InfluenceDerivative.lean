import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.InfluenceDerivative
open BooleanFourier


namespace BooleanFourier

/--
[boolDiscreteDerivative_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
lemma boolDiscreteDerivative_apply
  {n : ℕ}
  {g : (Fin (n + 1) → Bool) → ℝ}
  {i : Fin (n + 1)}
  {y : Fin n → Bool} :
-- imply
  boolDiscreteDerivative g i y = (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y)) :=
-- proof
  rfl

end BooleanFourier

namespace BooleanFourier

/--
[flipCoord_insertNth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
lemma flipCoord_insertNth
  {n : ℕ}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  flipCoord (Fin.insertNth i b y) i = Fin.insertNth i (!b) y := by
-- proof
  simp only [flipCoord, Fin.insertNth_apply_same]
  rw [Fin.update_insertNth]

end BooleanFourier

namespace BooleanFourier

/--
[ne_flipCoord_iff_insertNth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
lemma ne_flipCoord_iff_insertNth
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)}
  {b : Bool}
  {y : Fin n → Bool} :
-- imply
  (f (Fin.insertNth i b y) ≠ f (flipCoord (Fin.insertNth i b y) i)) ↔ (f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)) := by
-- proof
  rw [flipCoord_insertNth]
  cases b
  · exact ne_comm
  · rfl

end BooleanFourier

namespace BooleanFourier

/--
[influence_filter_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
lemma influence_filter_card_eq
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  (Finset.univ.filter fun x : Fin (n + 1) → Bool => f x ≠ f (flipCoord x i)).card = 2 * (Finset.univ.filter fun y : Fin n → Bool => f (Fin.insertNth i true y) ≠ f (Fin.insertNth i false y)).card := by
-- proof
  rw [Finset.card_filter, Finset.card_filter]
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Bool) i).symm
    (fun x : Fin (n + 1) → Bool => if f x ≠ f (flipCoord x i) then 1 else 0)
    (fun p : Bool × (Fin n → Bool) =>
      if f (Fin.insertNth i p.1 p.2) ≠ f (flipCoord (Fin.insertNth i p.1 p.2) i) then 1 else 0)
    (by intro p; simp)
  rw [h]
  simp_rw [ne_flipCoord_iff_insertNth f i]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul]

end BooleanFourier

namespace BooleanFourier

/--
[influence_eq_l2_norm_sq_discreteDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean)
-/
@[path]
lemma influence_eq_l2_norm_sq_discreteDerivative
  {n : ℕ}
  {f : (Fin (n + 1) → Bool) → Bool}
  {i : Fin (n + 1)} :
-- imply
  influence f i = (∑ y : Fin n → Bool, (boolDiscreteDerivative (fun x => boolToSign (f x)) i y) ^ 2) / (2 ^ n : ℝ) := by
-- proof
  have deriv_sq : ∀ y : Fin n → Bool,
    (boolDiscreteDerivative (fun x => boolToSign (f x)) i y) ^ 2 =
    if f (Fin.insertNth i true y) = f (Fin.insertNth i false y) then (0 : ℝ) else 1 := by
    intro y
    simp only [boolDiscreteDerivative, boolToSign]
    cases f (Fin.insertNth i true y) <;> cases f (Fin.insertNth i false y) <;> simp <;> norm_num
  simp_rw [deriv_sq]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, nsmul_eq_mul, mul_one]
  simp only [influence]
  rw [influence_filter_card_eq f i]
  push_cast
  rw [pow_succ]
  ring

end BooleanFourier


-- created on 2026-10-23
