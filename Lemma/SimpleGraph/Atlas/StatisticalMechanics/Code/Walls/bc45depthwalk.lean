import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc45_idx_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_idx_injective_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  Function.Injective (bc45_idx ω n) := by
-- proof
  apply StatMech.Walls.bc45_idx_injective ω n

/--
[bc45_root_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_root_reachable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (v : {x : Site d // x ∈ tfc_trifFinset ω n}) :
-- imply
  (bc37_armAdjGraph ω n).Reachable (bc45_root ω n v) v := by
-- proof
  apply StatMech.Walls.bc45_root_reachable ω n v

/--
[bc45_root_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_root_inv_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {v w : {x : Site d // x ∈ tfc_trifFinset ω n}}
-- given
  (h : (bc37_armAdjGraph ω n).Reachable v w) :
-- imply
  bc45_root ω n v = bc45_root ω n w := by
-- proof
  apply StatMech.Walls.bc45_root_inv ω n h

/--
[bc45_dep_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_dep_eq_zero_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {v : Site d}
-- given
  (hv : v ∈ tfc_trifFinset ω n) :
-- imply
  bc45_dep ω n v = 0 ↔ (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = bc45_root ω n ⟨v, hv⟩ := by
-- proof
  apply StatMech.Walls.bc45_dep_eq_zero_iff ω n v hv

/--
[bc45_par_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_par_spec_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {v : Site d}
-- given
  (hv : v ∈ tfc_trifFinset ω n)
  (hnonroot : (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨v, hv⟩) :
-- imply
  (bc45_armForestPar ω n v ∈ tfc_trifFinset ω n) ∧ bc37_ArmAdjacent ω n v (bc45_armForestPar ω n v) ∧ bc45_dep ω n (bc45_armForestPar ω n v) < bc45_dep ω n v := by
-- proof
  apply StatMech.Walls.bc45_par_spec ω n hv hnonroot

/--
[bc45_armEdge_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_armEdge_transfer_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b y : Site d}
-- given
  (hadj : bc37_ArmAdjacent ω n a b)
  (hyT : y ∈ tfc_trifFinset ω n)
  (hya : y ≠ a)
  (hyb : y ≠ b) :
-- imply
  Connected d (removeSite y ω) a b := by
-- proof
  apply StatMech.Walls.bc45_armEdge_transfer ω n hadj hyT hya hyb

/--
[bc45_rootward_reach_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_rootward_reach_root_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {y : Site d}
-- given
  (hyT : y ∈ tfc_trifFinset ω n) :
-- imply
  ∀ (v : Site d) (hv : v ∈ tfc_trifFinset ω n), bc45_dep ω n v < bc45_dep ω n y → Connected d (removeSite y ω) v (bc45_root ω n ⟨v, hv⟩).1 := by
-- proof
  apply StatMech.Walls.bc45_rootward_reach_root ω n hyT

/--
[bc45_armDepthRank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_armDepthRank_injective_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b → a ≠ b → Connected d ω a b → bc45_armDepthRank ω n a ≠ bc45_armDepthRank ω n b := by
-- proof
  apply StatMech.Walls.bc45_armDepthRank_injective ω n

/--
[bc45_rootWard_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_rootWard_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hxT : x ∈ tfc_trifFinset ω n)
  (hyT : y ∈ tfc_trifFinset ω n)
  (hxy : x ≠ y)
  (hconn : Connected d ω x y)
  (hlt : bc45_armDepthRank ω n x < bc45_armDepthRank ω n y)
  (hpadj : bc37_ArmAdjacent ω n y (bc45_armForestPar ω n y))
  (hparT : bc45_armForestPar ω n y ∈ tfc_trifFinset ω n)
  (_hprank : bc45_armDepthRank ω n (bc45_armForestPar ω n y) < bc45_armDepthRank ω n y) :
-- imply
  Connected d (removeSite y ω) x (bc45_armForestPar ω n y) := by
-- proof
  apply StatMech.Walls.bc45_rootWard_connected ω n hxT hyT hxy hconn hlt hpadj hparT _hprank

/--
[bc45_rootWardRootParent_holds_at_depthRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_rootWardRootParent_holds_at_depthRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc43_RootWardRootParent ω n (bc45_armDepthRank ω n) (bc45_armForestPar ω n) := by
-- proof
  apply StatMech.Walls.bc45_rootWardRootParent_holds_at_depthRank ω n

/--
[bc45_rooting_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_rooting_spec_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → bc45_armDepthRank ω n x < bc45_armDepthRank ω n y → bc45_armForestPar ω n y ∈ tfc_trifFinset ω n ∧ bc37_ArmAdjacent ω n y (bc45_armForestPar ω n y) ∧ bc45_armDepthRank ω n (bc45_armForestPar ω n y) < bc45_armDepthRank ω n y := by
-- proof
  apply StatMech.Walls.bc45_rooting_spec ω n

/--
[bc45_parentFunneling_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_parentFunneling_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc45_parentFunneling_of_cutGeometryFixed' ω n hgeo

/--
[bc45_selfDownArm_of_cutGeometryFixed'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_selfDownArm_of_cutGeometryFixed'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc45_selfDownArm_of_cutGeometryFixed' ω n hgeo

/--
[bc45_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc45_burton_keane_bernoulli hd p hp1 hp0 hgeo htrif

/--
[bc45_farSide_deeper_excluded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_farSide_deeper_excluded_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {y z : Site d}
-- given
  (hyT : y ∈ tfc_trifFinset ω n)
  (hyroot : (⟨y, hyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ bc45_root ω n ⟨y, hyT⟩)
  (hdeeper : bc45_dep ω n y < bc45_dep ω n z) :
-- imply
  z ≠ bc45_armForestPar ω n y := by
-- proof
  apply StatMech.Walls.bc45_farSide_deeper_excluded ω n hyT hyroot hdeeper

/--
[bc45_monotone_avoids_deeper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_monotone_avoids_deeper_eq
  {d : ℕ}
  {depY depV : ℕ}
-- given
  (hlt : depV < depY) :
-- imply
  ∀ depW, depW ≤ depV → depW ≠ depY := by
-- proof
  apply StatMech.Walls.bc45_monotone_avoids_deeper depY depV hlt

/--
[bc45_chainShadow_confirms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_chainShadow_confirms_eq
  {d : ℕ} :
-- imply
  (∀ v : Fin 3, v ≠ 0 → bc45_chainDep (bc45_chainPar v) < bc45_chainDep v) ∧ (bc45_chainDep 1 < bc45_chainDep 2 ∧ bc45_chainPar 1 ≠ 2) ∧ (∀ v : Fin 3, bc45_chainDep v < bc45_chainDep 1 → v ≠ 1) := by
-- proof
  apply StatMech.Walls.bc45_chainShadow_confirms

/--
[bc45_yTreeShadow_confirms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc45depthwalk.lean)
-/
@[path]
private lemma bc45_yTreeShadow_confirms_eq
  {d : ℕ} :
-- imply
  (∀ v : Fin 4, v ≠ 0 → bc45_yDep (bc45_yPar v) < bc45_yDep v) ∧ (bc45_yDep 1 < bc45_yDep 2 ∧ bc45_yPar 1 ≠ 2) ∧ (bc45_yPar 2 = 1 ∧ bc45_yPar 3 = 1) ∧ (∀ v : Fin 4, bc45_yDep v < bc45_yDep 2 → v ≠ 2) := by
-- proof
  apply StatMech.Walls.bc45_yTreeShadow_confirms


-- created on 2026-10-23
