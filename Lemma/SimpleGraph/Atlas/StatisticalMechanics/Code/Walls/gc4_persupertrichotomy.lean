import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc4_persupertrichotomy
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc4_gap_eq_mass_mul_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_eq_mass_mul_factor_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  aie_gap ends m φ A o x y = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Walls.gc4_gap_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ

/--
[gc4_factor_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_factor_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 ∨ asd_ghsBackboneFactor ends m o x y = 0 ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Walls.gc4_factor_trichotomy ends m o x y

/--
[gc4_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_mass_nonneg_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {φ : Finset ι → ℝ}
  {A : Finset V}
-- given
  (hφnn : ∀ K, 0 ≤ φ K) :
-- imply
  0 ≤ aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc4_mass_nonneg ends m φ hφnn A

/--
[gc4_factor_eq_one_of_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_factor_eq_one_of_none_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hnone : aie_noneConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 1 := by
-- proof
  apply StatMech.Walls.gc4_factor_eq_one_of_none ends m hnone

/--
[gc4_factor_eq_zero_of_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_factor_eq_zero_of_exactlyOne_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hnotall : ¬ aie_allConn ends m o x y)
  (hnotnone : ¬ aie_noneConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = 0 := by
-- proof
  apply StatMech.Walls.gc4_factor_eq_zero_of_exactlyOne ends m hnotall hnotnone

/--
[gc4_factor_eq_neg_two_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_factor_eq_neg_two_of_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hall : aie_allConn ends m o x y) :
-- imply
  asd_ghsBackboneFactor ends m o x y = -2 := by
-- proof
  apply StatMech.Walls.gc4_factor_eq_neg_two_of_all ends m hall

/--
[gc4_PerSuperTrichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_PerSuperTrichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -2) ∧ aie_gap ends m φ A o x y = aie_mass ends m φ A * c ∧ 0 ≤ aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc4_PerSuperTrichotomy ends m hnd A hm hox hoy hxy φ hφnn hφ

/--
[gc4_factor_pinned_by_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_factor_pinned_by_regime_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  (aie_noneConn ends m o x y → asd_ghsBackboneFactor ends m o x y = 1) ∧ ((¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y) → asd_ghsBackboneFactor ends m o x y = 0) ∧ (aie_allConn ends m o x y → asd_ghsBackboneFactor ends m o x y = -2) := by
-- proof
  apply StatMech.Walls.gc4_factor_pinned_by_regime ends m o x y

/--
[gc4_gap_value_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_value_none_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnone : aie_noneConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc4_gap_value_none ends m hnd A hm hox hoy hxy φ hφnn hφ hnone

/--
[gc4_gap_value_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_value_exactlyOne_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnotall : ¬ aie_allConn ends m o x y)
  (hnotnone : ¬ aie_noneConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = 0 := by
-- proof
  apply StatMech.Walls.gc4_gap_value_exactlyOne ends m hnd A hm hox hoy hxy φ hφ hnotall hnotnone

/--
[gc4_gap_value_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_value_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc4_gap_value_all ends m hnd A hm hox hoy hxy φ hφnn hφ hall

/--
[gc4_per_super_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_per_super_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  (aie_noneConn ends m o x y ∧ aie_gap ends m φ A o x y = aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A) ∨ ((¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y) ∧ aie_gap ends m φ A o x y = 0) ∨ (aie_allConn ends m o x y ∧ aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A) := by
-- proof
  apply StatMech.Walls.gc4_per_super_trichotomy ends m hnd A hm hox hoy hxy φ hφnn hφ

/--
[gc4_gap_sign_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_sign_none_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hnone : aie_noneConn ends m o x y) :
-- imply
  0 ≤ aie_gap ends m φ A o x y := by
-- proof
  apply StatMech.Walls.gc4_gap_sign_none ends m hnd A hm hox hoy hxy φ hφnn hφ hnone

/--
[gc4_gap_sign_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_persupertrichotomy.lean)
-/
@[path]
private lemma gc4_gap_sign_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc4_gap_sign_all ends m hnd A hm hox hoy hxy φ hφnn hφ hall


-- created on 2026-10-23
