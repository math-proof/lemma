import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsCycleClose.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[pcy_toSubgraph_neighbor_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_toSubgraph_neighbor_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hthin : mci_FourThin Vc)
  (hu : u ∈ Vc.support)
  (hv : v ∈ Vc.support)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ Vc.toSubgraph.neighborSet u := by
-- proof
  apply StatMech.Lattice.pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv hadj

/--
[pcy_thickPoint_of_three_support_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_thickPoint_of_three_support_neighbors_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v₁ v₂ v₃ : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hu : u ∈ Vc.support)
  (h0 : (hypercubicLattice 2).Adj u v₁)
  (h1 : (hypercubicLattice 2).Adj u v₂)
  (h2 : (hypercubicLattice 2).Adj u v₃)
  (hv1 : v₁ ∈ Vc.support)
  (hv2 : v₂ ∈ Vc.support)
  (hv3 : v₃ ∈ Vc.support)
  (hne12 : v₁ ≠ v₂)
  (hne13 : v₁ ≠ v₃)
  (hne23 : v₂ ≠ v₃) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.pcy_thickPoint_of_three_support_neighbors Vc hcyc hu h0 h1 h2 hv1 hv2 hv3 hne12 hne13 hne23

/--
[pcy_le_two_support_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_le_two_support_neighbors_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hthin : mci_FourThin Vc)
  (hu : u ∈ Vc.support) :
-- imply
  {v : Site 2 | (hypercubicLattice 2).Adj u v ∧ v ∈ Vc.support}.ncard ≤ 2 := by
-- proof
  apply StatMech.Lattice.pcy_le_two_support_neighbors Vc hcyc hthin hu

/--
[pcy_thickPoint_of_WES](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_thickPoint_of_WES_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hcyc : Vc.IsCycle)
  (hu : (![x, y] : Site 2) ∈ Vc.support)
  (hW : (![x - 1, y] : Site 2) ∈ Vc.support)
  (hE : (![x + 1, y] : Site 2) ∈ Vc.support)
  (hS : (![x, y - 1] : Site 2) ∈ Vc.support) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.pcy_thickPoint_of_WES Vc hcyc hu hW hE hS

/--
[pcy_fig8_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_eq_eq :
-- imply
  wpc_fig8 = pcy_fig8_A.append pcy_fig8_B := by
-- proof
  apply StatMech.Lattice.pcy_fig8_eq

/--
[pcy_fig8_A_not_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_A_not_nil_eq :
-- imply
  ¬ pcy_fig8_A.Nil := by
-- proof
  apply StatMech.Lattice.pcy_fig8_A_not_nil

/--
[pcy_fig8_B_not_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_B_not_nil_eq :
-- imply
  ¬ pcy_fig8_B.Nil := by
-- proof
  apply StatMech.Lattice.pcy_fig8_B_not_nil

/--
[pcy_fig8_not_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_not_cycle_eq :
-- imply
  ¬ wpc_fig8.IsCycle := by
-- proof
  apply StatMech.Lattice.pcy_fig8_not_cycle

/--
[pcy_crossArcThick_of_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_crossArcThick_of_crossArcThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcat : cat_CrossArcThick Vc seed) :
-- imply
  pcy_CrossArcThick Vc seed := by
-- proof
  apply StatMech.Lattice.pcy_crossArcThick_of_crossArcThick Vc hcat

/--
[pcy_noKingSeparation_of_fourThin_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_noKingSeparation_of_fourThin_cycle_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : pcy_CrossArcThick Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.pcy_noKingSeparation_of_fourThin_cycle Vc hcyc hseedI hthin hres

/--
[pcy_kingRowLinked_of_fourThin_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_kingRowLinked_of_fourThin_cycle_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : pcy_CrossArcThick Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.pcy_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hres

/--
[pcy_kingInteriorConnected_of_fourThin_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_kingInteriorConnected_of_fourThin_cycle_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ∀ seed ∈ jil_offSupportInterior Vc, pcy_CrossArcThick Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.pcy_kingInteriorConnected_of_fourThin_cycle Vc hcyc hz₀ hthin hres

/--
[pcy_fig8_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_crossArcThick_eq :
-- imply
  pcy_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_fig8_crossArcThick

/--
[pcy_fig8_structural_fix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fig8_structural_fix_eq :
-- imply
  ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) ∧ mci_FourThin wpc_fig8 ∧ ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) ∧ ¬ wpc_fig8.IsCycle ∧ pcy_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_fig8_structural_fix

/--
[pcy_fjord_on_32](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fjord_on_32_eq :
-- imply
  (![3, 2] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.pcy_fjord_on_32

/--
[pcy_fjord_on_30](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fjord_on_30_eq :
-- imply
  (![3, 0] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.pcy_fjord_on_30

/--
[pcy_fjord_throat_three_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fjord_throat_three_neighbors_eq :
-- imply
  (![3, 1] : Site 2) ∈ sdc_fjord.support ∧ (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 0] : Site 2) ∧ (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 2] : Site 2) ∧ (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![4, 1] : Site 2) ∧ (![3, 0] : Site 2) ∈ sdc_fjord.support ∧ (![3, 2] : Site 2) ∈ sdc_fjord.support ∧ (![4, 1] : Site 2) ∈ sdc_fjord.support ∧ (![3, 0] : Site 2) ≠ (![3, 2] : Site 2) ∧ (![3, 0] : Site 2) ≠ (![4, 1] : Site 2) ∧ (![3, 2] : Site 2) ≠ (![4, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_fjord_throat_three_neighbors

/--
[pcy_fjord_three_support_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fjord_three_support_neighbors_eq
-- given
  (hcyc : sdc_fjord.IsCycle) :
-- imply
  kns_ThickPoint sdc_fjord := by
-- proof
  apply StatMech.Lattice.pcy_fjord_three_support_neighbors hcyc

/--
[pcy_ksd_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_ksd_crossArcThick_eq :
-- imply
  pcy_CrossArcThick ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_ksd_crossArcThick

/--
[pcy_kda_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_kda_crossArcThick_eq :
-- imply
  pcy_CrossArcThick kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_kda_crossArcThick

/--
[pcy_fjord_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_fjord_crossArcThick_eq :
-- imply
  pcy_CrossArcThick sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.pcy_fjord_crossArcThick

/--
[pcy_kingRowLinked_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean)
-/
@[path]
private lemma pcy_kingRowLinked_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcyc : Vc.IsCycle)
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  pcy_CrossArcThick Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.pcy_kingRowLinked_summary Vc hcyc hseedI hthin


-- created on 2026-10-23
