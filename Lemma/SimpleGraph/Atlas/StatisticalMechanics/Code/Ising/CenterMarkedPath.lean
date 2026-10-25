import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
open Finset Matrix StatMech StatMech.Ising


/--
[sum_snoc_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma sum_snoc_reindex_eq
  [Fintype E]
  [DecidableEq E]
  [AddCommMonoid R]
  {m : Nat}
-- given
  (F : (Fin (m + 1) -> E) -> R) :
-- imply
  (∑ t, F t) = ∑ y : E × (Fin m -> E), F (Fin.snoc y.2 y.1) := by
-- proof
  apply StatMech.Ising.sum_snoc_reindex m F

/--
[sum_comm_three_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma sum_comm_three_last_eq
  [Fintype E₁]
  [Fintype E₂]
  [Fintype E₃]
  [AddCommMonoid R]
-- given
  (F : E₁ -> E₂ -> E₃ -> R) :
-- imply
  (∑ x, ∑ y, ∑ z, F x y z) = ∑ z, ∑ x, ∑ y, F x y z := by
-- proof
  apply StatMech.Ising.sum_comm_three_last F

/--
[transitionProduct_cons_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma transitionProduct_cons_snoc_eq
  [Fintype E]
  [DecidableEq E]
  [CommMonoid R]
  {A : Matrix E E R}
  {x y : E}
-- given
  (q : Fin (m + 1) -> E) :
-- imply
  (∏ k : Fin (m + 2), A ((Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E) k.castSucc) ((Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E) k.succ)) = A x (q 0) * (∏ k : Fin m, A (q k.castSucc) (q k.succ)) * A (q (Fin.last m)) y := by
-- proof
  apply StatMech.Ising.transitionProduct_cons_snoc A x y q

/--
[center_cons_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma center_cons_snoc_eq
  {n : Nat}
  {x y : E}
-- given
  (q : Fin (2 * n + 1) -> E) :
-- imply
  (Fin.cons x (Fin.snoc q y) : Fin (2 * n + 3) -> E) ⟨n + 1, by omega⟩ = q ⟨n, by omega⟩ := by
-- proof
  apply StatMech.Ising.center_cons_snoc n q x y

/--
[last_cons_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma last_cons_snoc_eq
  {m : Nat}
  {x y : E}
-- given
  (q : Fin (m + 1) -> E) :
-- imply
  (Fin.cons x (Fin.snoc q y) : Fin (m + 3) -> E) (Fin.last (m + 2)) = y := by
-- proof
  apply StatMech.Ising.last_cons_snoc m q x y

/--
[centerMarkedPathSum_eq_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CenterMarkedPath.lean)
-/
@[path]
private lemma centerMarkedPathSum_eq_sum_sq_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {n : Nat}
-- given
  (hSymm : ∀ i j, A i j = A j i)
  (a obs : E -> R) :
-- imply
  centerMarkedPathSum A a obs n = ∑ i, obs i * ((A ^ n) *ᵥ a) i ^ 2 := by
-- proof
  apply StatMech.Ising.centerMarkedPathSum_eq_sum_sq A hSymm a obs n


-- created on 2026-10-23
