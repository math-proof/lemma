import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc4_nonvacuity
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc4_residue_iff_noneLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_residue_iff_noneLe_eq
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
  GHS3SummedGapNonpos ends M A Φ o x y ↔ gc4_NoneLeTwiceAll ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ

/--
[gc4_noneLe_of_noNoneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_noneLe_of_noNoneConn_eq
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
  (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
  (hnone : ∀ m ∈ M, ¬ aie_noneConn ends m o x y) :
-- imply
  gc4_NoneLeTwiceAll ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_noneLe_of_noNoneConn ends M A Φ hΦnn hnone

/--
[gc4_noneLe_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_noneLe_of_allConnOnly_eq
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
  (hΦnn : ∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K)
  (hall : ∀ m ∈ M, aie_allConn ends m o x y) :
-- imply
  gc4_NoneLeTwiceAll ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_noneLe_of_allConnOnly ends M A Φ hΦnn hall

/--
[gc4_gap_neg_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_gap_neg_of_allConnOnly_eq
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
  ∀ m ∈ M, aie_gap ends m (Φ m) A o x y = -2 * aie_mass ends m (Φ m) A ∧ aie_gap ends m (Φ m) A o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc4_gap_neg_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall

/--
[gc4_noneLe_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_noneLe_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {Φ : Finset ι → Finset ι → ℝ}
  {o x y : V} :
-- imply
  gc4_NoneLeTwiceAll ends (∅ : Finset (Finset ι)) A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_noneLe_empty ends A Φ o x y

/--
[gc4_residue_of_noNoneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_residue_of_noNoneConn_eq
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
  (hnone : ∀ m ∈ M, ¬ aie_noneConn ends m o x y) :
-- imply
  GHS3SummedGapNonpos ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_residue_of_noNoneConn ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hnone

/--
[gc4_residue_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_residue_of_allConnOnly_eq
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
  GHS3SummedGapNonpos ends M A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_residue_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall

/--
[gc4_residue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_nonvacuity.lean)
-/
@[path]
private lemma gc4_residue_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {Φ : Finset ι → Finset ι → ℝ}
  {o x y : V} :
-- imply
  GHS3SummedGapNonpos ends (∅ : Finset (Finset ι)) A Φ o x y := by
-- proof
  apply StatMech.Walls.gc4_residue_empty ends A Φ o x y


-- created on 2026-10-23
