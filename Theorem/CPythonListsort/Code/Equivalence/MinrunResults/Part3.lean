/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
import Def.CPythonListsort.Code.Equivalence.MinrunResults.Part2
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

theorem minrunNextSpec_balanced (listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent) :
    let next := minrunNextSpec listlen current exponent
    next.result = listlen / 2 ^ exponent ∨
      next.result = minrunCeilDiv listlen (2 ^ exponent) := by
  let modulus := 2 ^ exponent
  let quotient := listlen / modulus
  let residual := listlen % modulus
  have hmodulus : 0 < modulus := by simp [modulus]
  have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
  have hdecompose : modulus * quotient + residual = listlen := Nat.div_add_mod listlen modulus
  have htotal : current + listlen = modulus * quotient + (current + residual) := by
    omega
  have hresult : (current + listlen) / modulus =
      quotient + (current + residual) / modulus := by
    rw [htotal, Nat.mul_add_div hmodulus]
  dsimp only [minrunNextSpec]
  rw [hresult]
  by_cases hcarry : current + residual < modulus
  · left
    rw [Nat.div_eq_of_lt hcarry]
    simp [quotient, modulus]
  · right
    have hcarryDiv : (current + residual) / modulus = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hcarryDiv]
    have hremainder : 0 < listlen % modulus := by
      change 0 < residual
      by_contra hzero
      have : residual = 0 := by omega
      omega
    rw [minrunCeilDiv_eq_succ listlen modulus hmodulus hremainder]

/-- Every exact-arithmetic output is either the floor or ceiling target, provided a divisible
list length starts with zero residual. -/
theorem minrunSpecTrace_balanced (calls listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent)
    (hzero : listlen % 2 ^ exponent = 0 → current = 0) :
    ∀ x ∈ (minrunSpecTrace calls listlen exponent current).outputs,
      x = listlen / 2 ^ exponent ∨
        x = minrunCeilDiv listlen (2 ^ exponent) := by
  induction calls generalizing current with
  | zero => simp [minrunSpecTrace]
  | succ calls ih =>
      let next := minrunNextSpec listlen current exponent
      have hnextCurrent : next.residual < 2 ^ exponent := by
        exact Nat.mod_lt _ (pow_pos (by omega) _)
      have hnextZero : listlen % 2 ^ exponent = 0 → next.residual = 0 := by
        intro hdivisible
        have hcurrentZero := hzero hdivisible
        simp [next, minrunNextSpec, hcurrentZero, hdivisible]
      have hhead := minrunNextSpec_balanced listlen exponent current hcurrent
      have htail := ih next.residual hnextCurrent hnextZero
      simp only [minrunSpecTrace, List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact hhead
      · exact htail x hx

end CPythonListsort
