import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.KingStepConnectClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ksc_reachableSet_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_reachableSet_saturated_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc) :
-- imply
  ksc_KingSaturated Vc {v | ∃ hv : v ∈ jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable ⟨v, hv⟩ ⟨seed, hseedI⟩} := by
-- proof
  apply StatMech.Lattice.ksc_reachableSet_saturated Vc hseedI

/--
[ksc_kingStepReachable_of_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_kingStepReachable_of_noKingSeparation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hns : ksc_NoKingSeparation Vc seed) :
-- imply
  ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩ := by
-- proof
  apply StatMech.Lattice.ksc_kingStepReachable_of_noKingSeparation Vc hseedI hns

/--
[ksc_kingRowLinked_of_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_kingRowLinked_of_noKingSeparation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hns : ksc_NoKingSeparation Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.ksc_kingRowLinked_of_noKingSeparation Vc hseedI hns

/--
[ksc_kingInteriorConnected_of_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_kingInteriorConnected_of_noKingSeparation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hns : ksc_NoKingSeparation Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.ksc_kingInteriorConnected_of_noKingSeparation Vc hseedI hns

/--
[ksc_saturated_absorbs_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_saturated_absorbs_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {s t : jil_offSupportInterior Vc}
  {w : (mci_interiorKingGraph Vc).Walk s t}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hsT : (s : Site 2) ∈ T) :
-- imply
  (t : Site 2) ∈ T := by
-- proof
  apply StatMech.Lattice.ksc_saturated_absorbs_walk Vc hsat hsT w

/--
[ksc_noKingSeparation_of_kingStepReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_noKingSeparation_of_kingStepReachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hreach : ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.ksc_noKingSeparation_of_kingStepReachable Vc hseedI hreach

/--
[ksc_noKingSeparation_iff_kingStepReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_noKingSeparation_iff_kingStepReachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc) :
-- imply
  ksc_NoKingSeparation Vc seed ↔ ∀ z : jil_offSupportInterior Vc, (mci_interiorKingGraph Vc).Reachable z ⟨seed, hseedI⟩ := by
-- proof
  apply StatMech.Lattice.ksc_noKingSeparation_iff_kingStepReachable Vc hseedI

/--
[ksc_saturated_axial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_saturated_axial_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {u v : Site 2}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hu : u ∈ T)
  (hvI : v ∈ jil_offSupportInterior Vc)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  v ∈ T := by
-- proof
  apply StatMech.Lattice.ksc_saturated_axial Vc hsat hu hvI hadj

/--
[ksc_saturated_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_saturated_diag_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y sx sy : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hsx : sx = 1 ∨ sx = -1)
  (hsy : sy = 1 ∨ sy = -1)
  (hxy : (![x, y] : Site 2) ∈ T)
  (hdI : (![x + sx, y + sy] : Site 2) ∈ jil_offSupportInterior Vc) :
-- imply
  (![x + sx, y + sy] : Site 2) ∈ T := by
-- proof
  apply StatMech.Lattice.ksc_saturated_diag Vc hsat hsx hsy hxy hdI

/--
[ksc_saturated_diagBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_saturated_diagBridge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hxy : (![x, y] : Site 2) ∈ T)
  (hxyI : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hdiag : (![x + 1, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (helb_off : (![x + 1, y] : Site 2) ∉ Vc.support) :
-- imply
  (![x + 1, y + 1] : Site 2) ∈ T := by
-- proof
  apply StatMech.Lattice.ksc_saturated_diagBridge Vc hsat hxy hxyI hdiag helb_off

/--
[ksc_separated_midOnSupport_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_separated_midOnSupport_horiz_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hL : (![x - 1, y] : Site 2) ∈ T)
  (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hRnT : (![x + 1, y] : Site 2) ∉ T) :
-- imply
  (![x, y] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ksc_separated_midOnSupport_horiz Vc hsat hTsub hL hR hRnT

/--
[ksc_separated_midOnSupport_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_separated_midOnSupport_vert_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hD : (![x, y - 1] : Site 2) ∈ T)
  (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hUnT : (![x, y + 1] : Site 2) ∉ T) :
-- imply
  (![x, y] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ksc_separated_midOnSupport_vert Vc hsat hTsub hD hU hUnT

/--
[ksc_interiorKing_reachable_of_kingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_interiorKing_reachable_of_kingWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  ∀ {z seed : Site 2} (p : mci_kingGraph.Walk z seed) (_hp : ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc) (hzI : z ∈ jil_offSupportInterior Vc) (hseedI : seed ∈ jil_offSupportInterior Vc), (mci_interiorKingGraph Vc).Reachable ⟨z, hzI⟩ ⟨seed, hseedI⟩ := by
-- proof
  apply StatMech.Lattice.ksc_interiorKing_reachable_of_kingWalk Vc

/--
[ksc_noKingSeparation_of_kingRowLinked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_noKingSeparation_of_kingRowLinked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hrl : mci_KingRowLinked Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.ksc_noKingSeparation_of_kingRowLinked Vc hseedI hrl

/--
[ksc_noKingSeparation_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_noKingSeparation_singleton_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hsingle : jil_offSupportInterior Vc = {seed}) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.ksc_noKingSeparation_singleton Vc hsingle

/--
[ksc_ksd_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_ksd_noKingSeparation_eq :
-- imply
  ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksc_ksd_noKingSeparation

/--
[ksc_kda_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_kda_noKingSeparation_eq :
-- imply
  ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksc_kda_noKingSeparation

/--
[ksc_fjord_col4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_col4_eq
  {r : ℤ}
-- given
  (h0 : 0 ≤ r)
  (h1 : r ≤ 3) :
-- imply
  (![4, r] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.ksc_fjord_col4 r h0 h1

/--
[ksc_fjord_col7](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_col7_eq
  {r : ℤ}
-- given
  (h0 : 0 ≤ r)
  (h1 : r ≤ 4) :
-- imply
  (![7, r] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.ksc_fjord_col7 r h0 h1

/--
[ksc_fjord_row0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_row0_eq
  {c : ℤ}
-- given
  (h0 : 4 ≤ c)
  (h1 : c ≤ 7) :
-- imply
  (![c, 0] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.ksc_fjord_row0 c h0 h1

/--
[ksc_fjord_row4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_row4_eq
  {c : ℤ}
-- given
  (h0 : 0 ≤ c)
  (h1 : c ≤ 7) :
-- imply
  (![c, 4] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.ksc_fjord_row4 c h0 h1

/--
[ksc_fjord_rp_king_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_rp_king_step_eq
  {u v : Site 2}
-- given
  (hu : u ∈ iwc_RightPocket)
  (hadj : mci_kingGraph.Adj u v)
  (hv : v ∉ sdc_fjord.support) :
-- imply
  v ∈ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.ksc_fjord_rp_king_step hu hadj hv

/--
[ksc_fjord_rp_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_rp_interior_eq
  {z : Site 2}
-- given
  (hz : z ∈ iwc_RightPocket) :
-- imply
  z ∈ jil_offSupportInterior sdc_fjord := by
-- proof
  apply StatMech.Lattice.ksc_fjord_rp_interior z hz

/--
[ksc_fjord_noKingSeparation_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_noKingSeparation_false_eq :
-- imply
  ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksc_fjord_noKingSeparation_false

/--
[ksc_fjord_rp_is_king_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_rp_is_king_separation_eq :
-- imply
  iwc_RightPocket ⊆ jil_offSupportInterior sdc_fjord ∧ ksc_KingSaturated sdc_fjord iwc_RightPocket ∧ ¬ jil_offSupportInterior sdc_fjord ⊆ iwc_RightPocket := by
-- proof
  apply StatMech.Lattice.ksc_fjord_rp_is_king_separation

/--
[ksc_saturated_absorbs_kingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_saturated_absorbs_kingWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
-- given
  (hsat : ksc_KingSaturated Vc T) :
-- imply
  ∀ {x y : Site 2} (q : mci_kingGraph.Walk x y), (∀ w ∈ q.support, w ∈ jil_offSupportInterior Vc) → x ∈ T → y ∈ T := by
-- proof
  apply StatMech.Lattice.ksc_saturated_absorbs_kingWalk Vc hsat

/--
[ksc_fjord_kingRowLinked_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_fjord_kingRowLinked_false_eq :
-- imply
  ¬ mci_KingRowLinked sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksc_fjord_kingRowLinked_false

/--
[ksc_kingRowLinked_iff_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingStepConnectClose.lean)
-/
@[path]
private lemma ksc_kingRowLinked_iff_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc) :
-- imply
  ksc_NoKingSeparation Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.ksc_kingRowLinked_iff_summary Vc hseedI


-- created on 2026-10-23
