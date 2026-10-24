import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc3_signedperSuper
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc3_signedPerSuper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_signedPerSuper_eq
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
  (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K) - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K) = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) * (1 - (if connK ends m x y then 1 else 0) - (if connK ends m o y then 1 else 0) - (if connK ends m o x then 1 else 0)) := by
-- proof
  apply StatMech.Walls.gc3_signedPerSuper ends m hnd A hm hox hoy hxy φ hφ

/--
[gc3_gap_eq_mass_mul_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_gap_eq_mass_mul_backbone_eq
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
  apply StatMech.Walls.gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ

/--
[gc3_gap_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_gap_allConn_eq
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
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc3_gap_allConn ends m hnd A hm hox hoy hxy φ hφ hall

/--
[gc3_gap_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_gap_noneConn_eq
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
  (hnone : aie_noneConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = aie_mass ends m φ A := by
-- proof
  apply StatMech.Walls.gc3_gap_noneConn ends m hnd A hm hox hoy hxy φ hφ hnone

/--
[gc3_gap_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_gap_exactlyOne_eq
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
  apply StatMech.Walls.gc3_gap_exactlyOne ends m hnd A hm hox hoy hxy φ hφ hnotall hnotnone

/--
[gc3_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_mass_nonneg_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {φ : Finset ι → ℝ}
  {S : Finset V}
-- given
  (hφnn : ∀ K, 0 ≤ φ K) :
-- imply
  0 ≤ aie_mass ends m φ S := by
-- proof
  apply StatMech.Walls.gc3_mass_nonneg ends m φ hφnn S

/--
[gc3_per_super_nonneg_not_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_signedperSuper.lean)
-/
@[path]
private lemma gc3_per_super_nonneg_not_all_eq
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
  (hnotall : ¬ aie_allConn ends m o x y) :
-- imply
  0 ≤ aie_gap ends m φ A o x y := by
-- proof
  apply StatMech.Walls.gc3_per_super_nonneg_not_all ends m hnd A hm hox hoy hxy φ hφnn hφ hnotall


-- created on 2026-10-23
