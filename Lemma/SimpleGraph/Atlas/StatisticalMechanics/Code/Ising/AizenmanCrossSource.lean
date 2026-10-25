import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanCrossSource.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising


/--
[gha_crossSource_mass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_crossSource_mass_eq_eq
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
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A ∧ aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A ∧ aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.gha_crossSource_mass_eq ends m hnd A hm hox hoy hxy φ hφ hall

/--
[gha_crossSource_total_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_crossSource_total_eq_eq
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
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {x, y}) + aie_mass ends m φ (A ∆ {o, y}) + aie_mass ends m φ (A ∆ {o, x}) = 3 * aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.gha_crossSource_total_eq ends m hnd A hm hox hoy hxy φ hφ hall

/--
[gha_allConn_gap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_allConn_gap_eq_eq
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
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.gha_allConn_gap_eq ends m hnd A hm hox hoy hxy φ hφ hall

/--
[gha_crossSource_singleton_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_crossSource_singleton_collapse_eq
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
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hall : aie_allConn ends m o x y) :
-- imply
  aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.gha_crossSource_singleton_collapse ends m hnd A hm hox hoy hxy φ hφ hall

/--
[gha_crossSourceDom_holds_of_no_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_crossSourceDom_holds_of_no_allConn_eq
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
  (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
  (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
-- imply
  gha_crossSourceDom ends M A o x y Φ := by
-- proof
  apply StatMech.Ising.gha_crossSourceDom_holds_of_no_allConn ends M A Φ hΦnn hno

/--
[gha_crossSource_hdom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanCrossSource.lean)
-/
@[path]
private lemma gha_crossSource_hdom_refutable_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ¬ gha_crossSourceDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
-- proof
  apply StatMech.Ising.gha_crossSource_hdom_refutable


-- created on 2026-10-23
