import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc4_massesle
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc4_masses_le_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_masses_le_of_residue_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hres : GHS3SummedGapNonpos ends M A Φ o x y) :
-- imply
  gc4_MassesLe ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_masses_le_of_residue ends M A o x y Φ hres

/--
[gc4_massesLe_iff_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_iff_residue_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ} :
-- imply
  gc4_MassesLe ends M A Φ o x y ↔ GHS3SummedGapNonpos ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_massesLe_iff_residue ends M A o x y Φ

/--
[gc4_massesLe_iff_noneLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_iff_noneLe_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  gc4_MassesLe ends M A Φ o x y ↔ (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Walls.gc4_massesLe_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ

/--
[gc4_massesLe_of_noneLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_of_noneLe_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hnone : (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)) :
-- imply
  gc4_MassesLe ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_massesLe_of_noneLe ends M hnd A hm hox hoy hxy Φ hΦ hnone

/--
[gc4_massesLe_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_of_allConnOnly_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, sources ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
-- imply
  gc4_MassesLe ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_massesLe_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall

/--
[gc4_massesLe_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {Φ : Finset ι → Finset ι → ℝ}
  {o x y : V} :
-- imply
  gc4_MassesLe ends (∅ : Finset (Finset ι)) A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_massesLe_empty ends A Φ o x y

/--
[gc4_massesLe_single_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean)
-/
@[path]
private lemma gc4_massesLe_single_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  gc4_MassesLe ends ({m} : Finset (Finset ι)) (sources ends m) (fun _ => φ) o x y := by
-- proof
  apply StatMech.Walls.gc4_massesLe_single_allConn ends m hnd hox hoy hxy φ hφnn hφ hall


-- created on 2026-10-23
