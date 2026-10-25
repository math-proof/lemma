import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc3_core.Part2
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc3_summedGap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_summedGap_eq_eq
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
  ∑ m ∈ M, aie_gap ends m (Φ m) A o x y = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Walls.gc3_summedGap_eq ends M hnd A hm hox hoy hxy Φ hΦ

/--
[gc3_residue_iff_noneLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_residue_iff_noneLe_eq
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
  GHS3SummedGapNonpos ends M A Φ o x y ↔ (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) ≤ 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Walls.gc3_residue_iff_noneLe ends M hnd A hm hox hoy hxy Φ hΦ

/--
[gc3_ghs_masses_le_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_ghs_masses_le_of_residue_eq
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
  (∑ m ∈ M, aie_mass ends m (Φ m) A) ≤ (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y})) + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y})) + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x})) := by
-- proof
  apply StatMech.Walls.gc3_ghs_masses_le_of_residue ends M A o x y Φ hres

/--
[gc3_residue_of_allConnOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_residue_of_allConnOnly_eq
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
  apply StatMech.Walls.gc3_residue_of_allConnOnly ends M hnd A hm hox hoy hxy Φ hΦnn hΦ hall

/--
[gc3_residue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_residue_empty_eq
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
  apply StatMech.Walls.gc3_residue_empty ends A Φ o x y

/--
[gc3_residue_single_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_residue_single_allConn_eq
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
  GHS3SummedGapNonpos ends ({m} : Finset (Finset ι)) (sources ends m) (fun _ => φ) o x y := by
-- proof
  apply StatMech.Walls.gc3_residue_single_allConn ends m hnd hox hoy hxy φ hφnn hφ hall

/--
[gc3_residue_not_termwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_residue_not_termwise_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m₁ m₂ : Finset ι}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd₁ : ∀ i ∈ m₁, ¬ (ends i).IsDiag)
  (hnd₂ : ∀ i ∈ m₂, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m₁ → K ⊆ m₁ → φ (K ∆ P) = φ K)
  (hφ' : ∀ K P, P ⊆ m₂ → K ⊆ m₂ → φ (K ∆ P) = φ K)
  (h₁ : aie_allConn ends m₁ o x y)
  (h₂ : aie_noneConn ends m₂ o x y) :
-- imply
  aie_gap ends m₁ φ (sources ends m₁) o x y ≤ 0 ∧ 0 ≤ aie_gap ends m₂ φ (sources ends m₂) o x y := by
-- proof
  apply StatMech.Walls.gc3_residue_not_termwise ends m₁ m₂ hnd₁ hnd₂ hox hoy hxy φ hφnn hφ hφ' h₁ h₂

/--
[gc3_ursell_nonpos_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_ursell_nonpos_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc3_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y

/--
[gc3_ghs_concavity_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_ghs_concavity_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc3_ghs_concavity_of_signDominance G β h hβ hh o hsd

/--
[gc3_aizenman_barsky_of_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_core.lean)
-/
@[path]
private lemma gc3_aizenman_barsky_of_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsd : GHSSignDominance G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc3_aizenman_barsky_of_signDominance G β h hβ hh o J hsd hfactor


-- created on 2026-10-23
