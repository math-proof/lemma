import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc112_separatedArmGraph_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_separatedArmGraph_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ : Site d}
-- given
  (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc112_separatedArmGraph_of_noTrif ω L R hno

/--
[bc112_separatedArmGraph_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_separatedArmGraph_of_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc106_SeparatedContractedTrifGraph ω L R) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc112_separatedArmGraph_of_full ω L R h

/--
[bc112_separatedArmGraph_of_bc103](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_separatedArmGraph_of_bc103_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc103_ContractedTrifGraph ω L R) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc112_separatedArmGraph_of_bc103 ω L R h

/--
[bc106_separatedContracted_of_gap1_gap2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc106_separatedContracted_of_gap1_gap2_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {S : Set (Site d)}
  {G : SimpleGraph (↑S : Type)}
  {ιU : Site d → (↑S : Type)}
-- given
  (hSfin : Fintype (↑S : Type))
  (hSne : Nonempty (↑S : Type))
  (hGdec : DecidableRel G.Adj)
  (hFdec : DecidableRel (osf_spanForest G).Adj)
  (hnbr : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∃ v₁ v₂ v₃ : (↑S : Type), G.Adj (ιU y) v₁ ∧ G.Adj (ιU y) v₂ ∧ G.Adj (ιU y) v₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₂ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₃ ∧ ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₂ v₃)
  (hιinj : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∀ z, z ∈ box d R → bc106_SeparatedCoarseTrif ω L z → ιU y = ιU z → y = z)
  (hmin : ∀ v, 1 ≤ (osf_spanForest G).degree v)
  (hleaf : ∀ v : (↑S : Type), (osf_spanForest G).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc106_separatedContracted_of_gap1_gap2 ω L R hSfin hSne G hGdec hFdec ιU hnbr hιinj hmin hleaf

/--
[bc112_leaf_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_coord0_eq
  {d : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d) :
-- imply
  bc112_leaf hd y k ⟨0, hd⟩ = y ⟨0, hd⟩ + k := by
-- proof
  apply StatMech.Walls.bc112_leaf_coord0 hd y k

/--
[bc112_leaf_coord_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_coord_ne_eq
  {d : ℕ}
  {y : Site d}
  {k : ℤ}
  {i : Fin d}
-- given
  (hd : 1 ≤ d)
  (hi : i ≠ ⟨0, hd⟩) :
-- imply
  bc112_leaf hd y k i = y i := by
-- proof
  apply StatMech.Walls.bc112_leaf_coord_ne hd y k hi

/--
[bc112_leaf_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_mem_box_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hk : k.natAbs ≤ L) :
-- imply
  bc112_leaf hd y k ∈ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bc112_leaf_mem_box hd y hk

/--
[bc112_leaf_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_inj_eq
  {d : ℕ}
  {y : Site d}
  {k k' : ℤ}
-- given
  (hd : 1 ≤ d)
  (hkk : k ≠ k') :
-- imply
  bc112_leaf hd y k ≠ bc112_leaf hd y k' := by
-- proof
  apply StatMech.Walls.bc112_leaf_inj hd y hkk

/--
[bc112_leaf_ne_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_ne_centre_eq
  {d : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hk : k ≠ 0) :
-- imply
  bc112_leaf hd y k ≠ y := by
-- proof
  apply StatMech.Walls.bc112_leaf_ne_centre hd y hk

/--
[bc112_shifts_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_shifts_ne_zero_eq
  {d : ℕ}
  {k : ℤ}
-- given
  (hk : k ∈ bc112_shifts) :
-- imply
  k ≠ 0 := by
-- proof
  apply StatMech.Walls.bc112_shifts_ne_zero hk

/--
[bc112_shifts_natAbs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_shifts_natAbs_le_eq
  {d : ℕ}
  {k : ℤ}
  {L : ℕ}
-- given
  (hk : k ∈ bc112_shifts)
  (hL : 3 ≤ L) :
-- imply
  k.natAbs ≤ L := by
-- proof
  apply StatMech.Walls.bc112_shifts_natAbs_le hk hL

/--
[bc112_mem_hubs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_mem_hubs_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d} :
-- imply
  y ∈ bc112_hubs ω L R ↔ y ∈ box d R ∧ bc106_SeparatedCoarseTrif ω L y := by
-- proof
  apply StatMech.Walls.bc112_mem_hubs

/--
[bc112_hubs_boxes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_hubs_boxes_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y z : Site d}
-- given
  (hy : y ∈ bc112_hubs ω L R)
  (hz : z ∈ bc112_hubs ω L R)
  (hne : y ≠ z) :
-- imply
  Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z) := by
-- proof
  apply StatMech.Walls.bc112_hubs_boxes_disjoint hy hz hne

/--
[bc112_starRel_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_starRel_symm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Symmetric (bc112_starRel hd ω L R) := by
-- proof
  apply StatMech.Walls.bc112_starRel_symm hd ω L R

/--
[bc112_leaf_mem_own_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_mem_own_box_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hk : k ∈ bc112_shifts) :
-- imply
  bc112_leaf hd y k ∈ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bc112_leaf_mem_own_box hd hL y hk

/--
[bc112_leaf_ne_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_ne_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y z : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hz : z ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts) :
-- imply
  bc112_leaf hd y k ≠ z := by
-- proof
  apply StatMech.Walls.bc112_leaf_ne_hub hd hL hy hz hk

/--
[bc112_leaf_ne_leaf_of_ne_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_ne_leaf_of_ne_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y z : Site d}
  {k k' : ℤ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hz : z ∈ bc112_hubs ω L R)
  (hyz : y ≠ z)
  (hk : k ∈ bc112_shifts)
  (hk' : k' ∈ bc112_shifts) :
-- imply
  bc112_leaf hd y k ≠ bc112_leaf hd z k' := by
-- proof
  apply StatMech.Walls.bc112_leaf_ne_leaf_of_ne_hub hd hL hy hz hyz hk hk'

/--
[bc112_leaf_same_hub_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_same_hub_inj_eq
  {d : ℕ}
  {y : Site d}
  {k k' : ℤ}
-- given
  (hd : 1 ≤ d)
  (h : bc112_leaf hd y k = bc112_leaf hd y k') :
-- imply
  k = k' := by
-- proof
  apply StatMech.Walls.bc112_leaf_same_hub_inj hd y h

/--
[bc112_hub_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_hub_mem_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
-- given
  (hd : 1 ≤ d)
  (hy : y ∈ bc112_hubs ω L R) :
-- imply
  y ∈ bc112_carrier hd ω L R := by
-- proof
  apply StatMech.Walls.bc112_hub_mem_carrier hd hy

/--
[bc112_leaf_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_mem_carrier_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hy : y ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts) :
-- imply
  bc112_leaf hd y k ∈ bc112_carrier hd ω L R := by
-- proof
  apply StatMech.Walls.bc112_leaf_mem_carrier hd hy hk

/--
[bc112_starRel_leaf_forces_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_starRel_leaf_forces_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k : ℤ}
  {w : Site d}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts)
  (h : bc112_starRel hd ω L R (bc112_leaf hd y k) w ∨ bc112_starRel hd ω L R w (bc112_leaf hd y k)) :
-- imply
  w = y := by
-- proof
  apply StatMech.Walls.bc112_starRel_leaf_forces_hub hd hL hy hk h

/--
[bc112_starGraph_leaf_adj_forces_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_starGraph_leaf_adj_forces_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k : ℤ}
  {lv w' : ↑(bc112_carrier hd ω L R)}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts)
  (hlv : (lv : Site d) = bc112_leaf hd y k)
  (hadj : (bc112_starGraph hd ω L R).Adj lv w') :
-- imply
  (w' : Site d) = y := by
-- proof
  apply StatMech.Walls.bc112_starGraph_leaf_adj_forces_hub hd hL hy hk hlv hadj

/--
[bc112_leaf_isolated_in_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaf_isolated_in_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k : ℤ}
  {w' : ↑(bc112_carrier hd ω L R)}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts)
  (hub lv : ↑(bc112_carrier hd ω L R))
  (hhub : (hub : Site d) = y)
  (hlv : (lv : Site d) = bc112_leaf hd y k) :
-- imply
  ¬ ((bc112_starGraph hd ω L R).deleteIncidenceSet hub).Adj lv w' := by
-- proof
  apply StatMech.Walls.bc112_leaf_isolated_in_cut hd hL hy hk hub lv hhub hlv w'

/--
[bc112_leaves_not_reachable_in_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_leaves_not_reachable_in_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k₁ k₂ : ℤ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L)
  (hy : y ∈ bc112_hubs ω L R)
  (hk₁ : k₁ ∈ bc112_shifts)
  (hk₂ : k₂ ∈ bc112_shifts)
  (hub lv₁ lv₂ : ↑(bc112_carrier hd ω L R))
  (hhub : (hub : Site d) = y)
  (hlv₁ : (lv₁ : Site d) = bc112_leaf hd y k₁)
  (hlv₂ : (lv₂ : Site d) = bc112_leaf hd y k₂)
  (hne : lv₁ ≠ lv₂) :
-- imply
  ¬ ((bc112_starGraph hd ω L R).deleteIncidenceSet hub).Reachable lv₁ lv₂ := by
-- proof
  apply StatMech.Walls.bc112_leaves_not_reachable_in_cut hd hL hy hk₁ hk₂ hub lv₁ lv₂ hhub hlv₁ hlv₂ hne

/--
[bc112_starGraph_hub_adj_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_starGraph_hub_adj_leaf_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y : Site d}
  {k : ℤ}
-- given
  (hd : 1 ≤ d)
  (hy : y ∈ bc112_hubs ω L R)
  (hk : k ∈ bc112_shifts)
  (hub lv : ↑(bc112_carrier hd ω L R))
  (hhub : (hub : Site d) = y)
  (hlv : (lv : Site d) = bc112_leaf hd y k) :
-- imply
  (bc112_starGraph hd ω L R).Adj hub lv := by
-- proof
  apply StatMech.Walls.bc112_starGraph_hub_adj_leaf hd hy hk hub lv hhub hlv

/--
[bc112_separatedArmGraph_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_separatedArmGraph_holds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hd : 1 ≤ d)
  (hL : 3 ≤ L) :
-- imply
  bc112_SeparatedArmGraph ω L R := by
-- proof
  apply StatMech.Walls.bc112_separatedArmGraph_holds hd ω L R hL

/--
[bc112_boundaryLeafResidue_iff_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_boundaryLeafResidue_iff_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc112_boundaryLeafResidue_iff_full ω L R

/--
[bc112_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean)
-/
@[path]
private lemma bc112_status_eq
  {d : ℕ} :
-- imply
  (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L → bc112_SeparatedArmGraph ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc103_ContractedTrifGraph ω L R → bc112_SeparatedArmGraph ω L R) := by
-- proof
  apply StatMech.Walls.bc112_status


-- created on 2026-10-23
