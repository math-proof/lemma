import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.BoxMengerAttachment
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bma_internal_of_edgesIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_internal_of_edgesIn_eq
  {d : ℕ}
  {R : Set (Site d)}
  {W : Finset (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ R) :
-- imply
  ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
-- proof
  apply StatMech.Percolation.bma_internal_of_edgesIn hW

/--
[bma_internal_of_edgesIn_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_internal_of_edgesIn_disjoint_eq
  {d : ℕ}
  {R S : Set (Site d)}
  {W : Finset (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, ∀ p, p ∈ e → p ∈ S)
  (hdisj : Disjoint R S) :
-- imply
  ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R := by
-- proof
  apply StatMech.Percolation.bma_internal_of_edgesIn_disjoint hW hdisj

/--
[bma_internal_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_internal_union_eq
  {d : ℕ}
  {R₁ R₂ R₃ : Set (Site d)}
  {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
-- given
  (h0 : ∀ e ∈ W₁, ∀ p, p ∈ e → p ∈ R₁)
  (h1 : ∀ e ∈ W₂, ∀ p, p ∈ e → p ∈ R₂)
  (h2 : ∀ e ∈ W₃, ∀ p, p ∈ e → p ∈ R₃)
  (hd12 : Disjoint R₁ R₂)
  (hd13 : Disjoint R₁ R₃) :
-- imply
  ∀ u v, u ∈ R₁ → s(u, v) ∈ W₁ ∪ W₂ ∪ W₃ → v ∈ R₁ := by
-- proof
  apply StatMech.Percolation.bma_internal_union h0 h1 h2 hd12 hd13

/--
[bma_originAvoiding_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_originAvoiding_union_eq
  {d : ℕ}
  {W₁ W₂ W₃ : Finset (Sym2 (Site d))}
-- given
  (h0 : ∀ e ∈ W₁, (0 : Site d) ∉ e)
  (h1 : ∀ e ∈ W₂, (0 : Site d) ∉ e)
  (h2 : ∀ e ∈ W₃, (0 : Site d) ∉ e) :
-- imply
  ∀ e ∈ W₁ ∪ W₂ ∪ W₃, (0 : Site d) ∉ e := by
-- proof
  apply StatMech.Percolation.bma_originAvoiding_union h0 h1 h2

/--
[bma_removeSite_forceOpen_mono_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_removeSite_forceOpen_mono_sub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {Wⱼ W : Finset (Sym2 (Site d))}
-- given
  (hsub : Wⱼ ⊆ W) :
-- imply
  removeSite 0 (forceOpenFinset Wⱼ ω) ≤ removeSite 0 (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.bma_removeSite_forceOpen_mono_sub ω hsub

/--
[bma_connected_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_connected_of_sub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {Wⱼ W : Finset (Sym2 (Site d))}
-- given
  (hsub : Wⱼ ⊆ W)
  (hc : Connected d (removeSite 0 (forceOpenFinset Wⱼ ω)) a x) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset W ω)) a x := by
-- proof
  apply StatMech.Percolation.bma_connected_of_sub ω hsub hc

/--
[bma_attachment_of_three_clusterAttachments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_attachment_of_three_clusterAttachments_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : bma_ClusterAttachment ω x₁)
  (h1 : bma_ClusterAttachment ω x₂)
  (h2 : bma_ClusterAttachment ω x₃) :
-- imply
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))), ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (∀ e ∈ W, (0 : Site d) ∉ e) ∧ (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧ ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧ (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧ (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧ (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
-- proof
  apply StatMech.Percolation.bma_attachment_of_three_clusterAttachments ω x₁ x₂ x₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[bma_boxMengerAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_boxMengerAttachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bma_BoxClusterAttachment d n) :
-- imply
  bmm_BoxMengerAttachment d n := by
-- proof
  apply StatMech.Percolation.bma_boxMengerAttachment h

/--
[bma_boxMergeFreeInsertion_of_clusterAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_boxMergeFreeInsertion_of_clusterAttachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bma_BoxClusterAttachment d n) :
-- imply
  tre_BoxMergeFreeInsertion d n := by
-- proof
  apply StatMech.Percolation.bma_boxMergeFreeInsertion_of_clusterAttachment h

/--
[bma_disjointRouting_of_clusterAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_disjointRouting_of_clusterAttachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bma_BoxClusterAttachment d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.bma_disjointRouting_of_clusterAttachment h

/--
[bma_clusterAttachment_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_clusterAttachment_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.bma_clusterAttachment_of_neighbour ω x hadj hri

/--
[bma_three_clusterAttachments_of_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean)
-/
@[path]
private lemma bma_three_clusterAttachments_of_neighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  bma_ClusterAttachment ω x₁ ∧ bma_ClusterAttachment ω x₂ ∧ bma_ClusterAttachment ω x₃ := by
-- proof
  apply StatMech.Percolation.bma_three_clusterAttachments_of_neighbours ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23
