import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.LatticePointCubeSandwich
open MeasureTheory Set ENNReal Pointwise
open LatticePointCubeSandwich


/--
[mem_integerUnitCube_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_integerUnitCube_iff_eq
  {n : ℕ}
  {v : Fin n → ℤ}
  {x : Fin n → ℝ} :
-- imply
  x ∈ integerUnitCube v ↔ ∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1 := by
-- proof
  apply LatticePointCubeSandwich.mem_integerUnitCube_iff

/--
[mem_outerCubeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_outerCubeSet_iff_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
  {v : Fin n → ℤ} :
-- imply
  v ∈ outerCubeSet S t ↔ ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S := by
-- proof
  apply LatticePointCubeSandwich.mem_outerCubeSet_iff

/--
[mem_innerCubeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_innerCubeSet_iff_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
  {v : Fin n → ℤ} :
-- imply
  v ∈ innerCubeSet S t ↔ ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S := by
-- proof
  apply LatticePointCubeSandwich.mem_innerCubeSet_iff

/--
[innerCubeSet_subset_outerCubeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma innerCubeSet_subset_outerCubeSet_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ} :
-- imply
  innerCubeSet S t ⊆ outerCubeSet S t := by
-- proof
  apply LatticePointCubeSandwich.innerCubeSet_subset_outerCubeSet S t

/--
[finite_outerCubeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma finite_outerCubeSet_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
-- given
  (hS : Bornology.IsBounded S)
  (ht : 0 < t) :
-- imply
  (outerCubeSet S t).Finite := by
-- proof
  apply LatticePointCubeSandwich.finite_outerCubeSet S hS ht

/--
[cube_measure_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma cube_measure_sandwich_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
-- given
  (hS : Bornology.IsBounded S)
  (ht : 0 < t) :
-- imply
  (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n ∧
    (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
-- proof
  apply LatticePointCubeSandwich.cube_measure_sandwich S hS ht


-- created on 2026-10-20
