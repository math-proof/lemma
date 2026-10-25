import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tfe_threeMeetBox_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_threeMeetBox_of_top_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htop : numInfiniteClusters d ω = ⊤) :
-- imply
  ∃ n : ℕ, ω ∈ threeMeetBox d n := by
-- proof
  apply StatMech.Percolation.tfe_threeMeetBox_of_top ω htop

/--
[tfe_three_distinct_infinite_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_three_distinct_infinite_of_box_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, (x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n) ∧ ((cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite) ∧ (cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃) := by
-- proof
  apply StatMech.Percolation.tfe_three_distinct_infinite_of_box hω

/--
[tfe_modification_preserves_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_modification_preserves_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {R₁ R₂ R₃ : Set (Site d)}
-- given
  (hm1 : a₁ ∈ R₁)
  (hm2 : a₂ ∈ R₂)
  (hm3 : a₃ ∈ R₃)
  (ho1 : ∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁)
  (ho2 : ∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂)
  (ho3 : ∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)
  (hg1 : ∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁)
  (hg2 : ∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂)
  (hg3 : ∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)
  (hd12 : Disjoint R₁ R₂)
  (hd13 : Disjoint R₁ R₃)
  (hd23 : Disjoint R₂ R₃) :
-- imply
  (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₂) ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) ∧ (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) := by
-- proof
  apply StatMech.Percolation.tfe_modification_preserves_distinct ω W a₁ a₂ a₃ R₁ R₂ R₃ hm1 hm2 hm3 ho1 ho2 ho3 hg1 hg2 hg3 hd12 hd13 hd23

/--
[tfe_threeClustersReachOrigin_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_threeClustersReachOrigin_of_attach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃)
  (h : tex_AttachData ω x₁ x₂ x₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tfe_threeClustersReachOrigin_of_attach ω x₁ x₂ x₃ hd h

/--
[tfe_threeClustersReachOrigin_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_threeClustersReachOrigin_of_top_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htop : numInfiniteClusters d ω = ⊤)
  (hres : ∀ m : ℕ, tfe_BoxAttachResidue d m) :
-- imply
  ∃ (n : ℕ) (W : Finset (Sym2 (Site d))), ω ∈ threeMeetBox d n ∧ mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tfe_threeClustersReachOrigin_of_top ω htop hres

/--
[tfe_routing_of_boxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_routing_of_boxResidue_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tfe_BoxAttachResidue d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.tfe_routing_of_boxResidue h

/--
[tfe_reachOrigin_of_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_reachOrigin_of_contact_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tfe_TrifurcationContact ω) :
-- imply
  mco_ThreeClustersReachOrigin ω := by
-- proof
  apply StatMech.Percolation.tfe_reachOrigin_of_contact ω h

/--
[tfe_contact_of_reachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_contact_of_reachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  tfe_TrifurcationContact ω := by
-- proof
  apply StatMech.Percolation.tfe_contact_of_reachOrigin ω h

/--
[tfe_reachOrigin_iff_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_reachOrigin_iff_contact_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  mco_ThreeClustersReachOrigin ω ↔ tfe_TrifurcationContact ω := by
-- proof
  apply StatMech.Percolation.tfe_reachOrigin_iff_contact ω

/--
[tfe_contact_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_contact_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
  (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
  (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  tfe_TrifurcationContact ω := by
-- proof
  apply StatMech.Percolation.tfe_contact_of_neighbour_witnesses ω a₁ a₂ a₃ hadj hi1 hi2 hi3 hd12 hd13 hd23

/--
[tfe_reachOrigin_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_reachOrigin_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
  (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
  (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  mco_ThreeClustersReachOrigin ω := by
-- proof
  apply StatMech.Percolation.tfe_reachOrigin_of_neighbour_witnesses ω a₁ a₂ a₃ hadj hi1 hi2 hi3 hd12 hd13 hd23

/--
[tfe_attach_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean)
-/
@[path]
private lemma tfe_attach_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.tfe_attach_nonvacuous ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23
