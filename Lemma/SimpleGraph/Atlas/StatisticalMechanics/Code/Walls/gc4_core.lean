import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc4_core
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc4_core_residue_iff_noneLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_core_residue_iff_noneLe_eq
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
  GHS3SummedGapNonpos ends M A Φ o x y ↔ ((∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)) := by
-- proof
  apply StatMech.Walls.gc4_core_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ

/--
[gc4_within_super_massShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_within_super_massShift_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {S : Finset V}
  {φ : Finset ι → ℝ}
-- given
  (hK : K ⊆ m)
  (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
-- imply
  aie_mass ends m φ (S ∆ sources ends K) = aie_mass ends m φ S := by
-- proof
  apply StatMech.Walls.gc4_within_super_massShift ends m K hK S φ hφ

/--
[gc4_shift_preserves_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_shift_preserves_factor_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hK : K ⊆ m) :
-- imply
  asd_ghsBackboneFactor ends m o x y = asd_ghsBackboneFactor ends m o x y ∧ Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_preserves_factor ends m K hK A o x y

/--
[gc4_shift_cannot_cross_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_shift_cannot_cross_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
-- given
  (h₁ : aie_allConn ends m₁ o x y)
  (h₂ : aie_noneConn ends m₂ o x y) :
-- imply
  asd_ghsBackboneFactor ends m₁ o x y = -2 ∧ asd_ghsBackboneFactor ends m₂ o x y = 1 ∧ asd_ghsBackboneFactor ends m₁ o x y ≠ asd_ghsBackboneFactor ends m₂ o x y := by
-- proof
  apply StatMech.Walls.gc4_shift_cannot_cross_class ends m₁ m₂ h₁ h₂

/--
[gc4_classes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_classes_disjoint_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hnone : aie_noneConn ends m o x y)
  (hall : aie_allConn ends m o x y) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.gc4_classes_disjoint ends m hnone hall

/--
[gc4_aie_mass_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_aie_mass_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {φ : Finset ι → ℝ}
  {S : Finset V} :
-- imply
  aie_mass ends (∅ : Finset ι) φ S = if S = ∅ then φ ∅ else 0 := by
-- proof
  apply StatMech.Walls.gc4_aie_mass_empty ends φ S

/--
[gc4_gap_empty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_gap_empty_pos_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {φ : Finset ι → ℝ}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  aie_gap ends (∅ : Finset ι) φ (∅ : Finset V) o x y = φ ∅ := by
-- proof
  apply StatMech.Walls.gc4_gap_empty_pos ends φ hox hoy hxy

/--
[gc4_abstract_residue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_abstract_residue_false_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {o x y : V}
  {ends : ι → Sym2 V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ¬ GHS3SummedGapNonpos ends ({∅} : Finset (Finset ι)) (∅ : Finset V) (fun _ _ => (1 : ℝ)) o x y := by
-- proof
  apply StatMech.Walls.gc4_abstract_residue_false hox hoy hxy ends

/--
[gc4_residue_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_residue_refutable_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {o x y : V}
  {ends : ι → Sym2 V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ¬ (∀ (M : Finset (Finset ι)) (A : Finset V) (Φ : Finset ι → Finset ι → ℝ), (∀ m ∈ M, ∀ K, 0 ≤ (Φ m) K) → GHS3SummedGapNonpos ends M A Φ o x y) := by
-- proof
  apply StatMech.Walls.gc4_residue_refutable hox hoy hxy ends

/--
[gc4_core_masses_le_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_core_masses_le_of_residue_eq
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
  apply StatMech.Walls.gc4_core_masses_le_of_residue ends M A o x y Φ hres

/--
[gc4_core_concavity_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_core_concavity_sharpness_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {o : W}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : ∀ h', 0 ≤ h' → GHSSignDominance G β h' o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  GHSThreePointSym G β h o ∧ ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) ∧ bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc4_core_concavity_sharpness G β h hβ hh o J hsd hfactor

/--
[gc4_core_residue_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_core_residue_of_allConnOnly_eq
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
  apply StatMech.Walls.gc4_core_residue_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall

/--
[gc4_core_residue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_core_residue_empty_eq
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
  apply StatMech.Walls.gc4_core_residue_empty ends A Φ o x y

/--
[gc4_genuine_object_is_ensemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_core.lean)
-/
@[path]
private lemma gc4_genuine_object_is_ensemble_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 W → ℝ}
  {M : Finset (Ising.Current W)}
  {B : Finset W}
  {o x y : W}
  {μ : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hμ : 0 ≤ μ) :
-- imply
  (-2 * μ * tcp_allConnProb G β J M B o x y ≤ 0) ∧ tcp_allConnProb G β J M B o x y ≤ 1 := by
-- proof
  apply StatMech.Walls.gc4_genuine_object_is_ensemble G β J hβ hJ M B o x y μ hμ


-- created on 2026-10-23
