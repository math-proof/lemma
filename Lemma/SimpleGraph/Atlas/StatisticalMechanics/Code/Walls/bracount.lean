import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bracount
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bra_G_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_G_le_lattice_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ} :
-- imply
  bri2_G ω L ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Walls.bra_G_le_lattice ω L

/--
[bra_ray_crux_transfers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_ray_crux_transfers_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {T : SimpleGraph (Site 2)}
  [LocallyFinite T]
  {w x : Site 2}
  {R : ℕ}
-- given
  (hT : T ≤ bri2_G ω L)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box 2 R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R) := by
-- proof
  apply StatMech.Walls.bra_ray_crux_transfers ω L T hT hR hwx hw hinf

/--
[bra_hub_cut_of_centreSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_hub_cut_of_centreSep_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j k₁ k₂ k₃ : Site 2}
-- given
  (h₁₂ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (bgf2_centre L k₁) (bgf2_centre L k₂))
  (h₁₃ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (bgf2_centre L k₁) (bgf2_centre L k₃))
  (h₂₃ : ¬ (bkg_deleteVertex (bgf2_Gf ω L) (bgf2_centre L j)).Reachable (bgf2_centre L k₂) (bgf2_centre L k₃)) :
-- imply
  ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₁ k₂ ∧ ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₁ k₃ ∧ ¬ (bkg_deleteVertex (bri2_G ω L) j).Reachable k₂ k₃ := by
-- proof
  apply StatMech.Walls.bra_hub_cut_of_centreSep ω L h₁₂ h₁₃ h₂₃

/--
[bra_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_count_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {S : Finset (Site 2)}
  {T : SimpleGraph {v // v ∈ S}}
  [DecidableRel T.Adj]
  [Fintype ι]
-- given
  (hTH : T ≤ bfct_restrict (bri2_G ω L) S)
  (hT : T.IsTree)
  (f : ι → {v // v ∈ S})
  (hf : Function.Injective f)
  (hcut : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧ ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧ ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧ ¬ (bkg_deleteVertex (bri2_G ω L) (f i : Site 2)).Reachable (a₂ : Site 2) (a₃ : Site 2))
  (B : Finset {v // v ∈ S})
  (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bra_count ω L S hTH hT f hf hcut B hleaf

/--
[bra_armImage_centre_iff_hubBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_armImage_centre_iff_hubBox_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {a : Site 2}
-- given
  (h0 : bgf2_IndexAllOpen ω L 0) :
-- imply
  bgf2_q ω L a = 0 ↔ a ∈ bc61_boxAround 2 L 0 := by
-- proof
  apply StatMech.Walls.bra_armImage_centre_iff_hubBox h0 a

/--
[bra_strictLoss_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_strictLoss_witness_eq
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0) := by
-- proof
  apply StatMech.Walls.bra_strictLoss_witness hL

/--
[bra_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_datum_implies_count_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bra_datum_implies_count ω L R h

/--
[bra_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bracount.lean)
-/
@[path]
private lemma bra_status_eq :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bri2_G ω L ≤ hypercubicLattice 2) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ bri2_G ω L → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R → (ray34_AvoidCluster T {x} w).Infinite → ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧ (∀ L : ℕ, 1 ≤ L → ¬ bgf2_IndexAllOpen (bao_onlyBox0 L) L (bc57_pt 1 0)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
-- proof
  apply StatMech.Walls.bra_status


-- created on 2026-10-23
