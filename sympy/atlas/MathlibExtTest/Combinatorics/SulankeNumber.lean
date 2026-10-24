/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SulankeNumber.lean -/


import sympy.atlas.Combinatorics.SulankeNumber
import Lemma.Finset.SulankeNumber
import Mathlib.Tactic

open MetaMathlibExt

example : sulankeB 0 0 = 1 := rfl
example : sulankeB 0 1 = 0 := rfl
example : sulankeB 0 2 = 0 := rfl
example : sulankeA 0 0 = 0 := rfl
example : sulankeA 0 3 = 0 := rfl

example : sulankeA 1 0 = 1 := rfl
example : sulankeA 1 1 = 2 := rfl
example : sulankeA 1 2 = 0 := rfl
example : sulankeB 1 0 = 1 := rfl
example : sulankeB 1 1 = 3 := rfl
example : sulankeB 1 2 = 2 := rfl
example : sulankeB 1 3 = 0 := rfl

example : sulankeA 2 0 = 1 := rfl
example : sulankeA 2 1 = 5 := rfl
example : sulankeA 2 2 = 8 := rfl
example : sulankeA 2 3 = 4 := rfl
example : sulankeA 2 4 = 0 := rfl
example : sulankeB 2 0 = 1 := rfl
example : sulankeB 2 1 = 6 := rfl
example : sulankeB 2 2 = 13 := rfl
example : sulankeB 2 3 = 12 := rfl
example : sulankeB 2 4 = 4 := rfl
example : sulankeB 2 5 = 0 := rfl

example : sulankeB 1 5 = 0 := sulankeB_eq_zero_of_two_mul_lt 1 5 (by omega)
example : sulankeA 1 4 = 0 := sulankeA_eq_zero_of_two_mul_le 1 4 (by omega)
example : sulankeB 2 7 = 0 := sulankeB_eq_zero_of_two_mul_lt 2 7 (by omega)
example : sulankeA 2 6 = 0 := sulankeA_eq_zero_of_two_mul_le 2 6 (by omega)

example : sulankeB 0 0 = 1 := sulankeB_zero
example : sulankeB 0 1 = 0 := sulankeB_zero_succ 0
example : sulankeA 1 0 = sulankeB 0 0 := sulankeA_succ_zero 0
example : sulankeA 2 2 = sulankeB 1 2 + 2 * sulankeB 1 1 := sulankeA_succ_succ 1 1
example : sulankeA 3 4 = sulankeB 2 4 + 2 * sulankeB 2 3 := sulankeA_succ_succ 2 3
example : sulankeB 1 0 = sulankeA 1 0 := sulankeB_succ_zero 0
example : sulankeB 2 0 = sulankeA 2 0 := sulankeB_succ_zero 1
example : sulankeB 1 1 = sulankeA 1 1 + sulankeA 1 0 := sulankeB_succ_succ 0 0
example : sulankeB 1 2 = sulankeA 1 2 + sulankeA 1 1 := sulankeB_succ_succ 0 1
example : sulankeB 2 3 = sulankeA 2 3 + sulankeA 2 2 := sulankeB_succ_succ 1 2
