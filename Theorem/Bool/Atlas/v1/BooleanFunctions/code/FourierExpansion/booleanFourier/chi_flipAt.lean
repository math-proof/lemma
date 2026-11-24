module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.flipAt_ne_self
open Finset BigOperators BooleanFourier Bool


public section

/--
[chi_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {S : Finset (Fin n)}
  {j : Fin n}
  {x : Fin n → Bool}
-- given
  (hj : j ∈ S) :
-- imply
  chi S (flipAt j x) = -chi S x := by
-- proof
  simp only [chi, flipAt]
  have hlhs : ∏ i ∈ S, boolToReal (Function.update x j (!x j) i) =
    boolToReal (Function.update x j (!x j) j) *
    ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) :=
    (Finset.mul_prod_erase S _ hj).symm
  have hrhs : ∏ i ∈ S, boolToReal (x i) =
    boolToReal (x j) * ∏ i ∈ S.erase j, boolToReal (x i) :=
    (Finset.mul_prod_erase S _ hj).symm
  rw [hlhs, hrhs]
  have h1 : boolToReal (Function.update x j (!x j) j) = -boolToReal (x j) := by
    simp [Function.update_self, boolToReal_not]
  have h2 : ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) =
    ∏ i ∈ S.erase j, boolToReal (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [h1, h2]
  ring


theorem BooleanFourier.chi_flipAt
  {n : ℕ}
  {S : Finset (Fin n)}
  {j : Fin n}
  {x : Fin n → Bool}
-- given
  (hj : j ∈ S) :
-- imply
  chi S (flipAt j x) = -chi S x :=
-- proof
  main hj


-- created on 2026-10-23
-- updated on 2026-11-24
