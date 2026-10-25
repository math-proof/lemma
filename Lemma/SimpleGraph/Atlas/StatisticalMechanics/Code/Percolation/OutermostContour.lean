import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour.Part2
open Finset Set SimpleGraph Function StatMech StatMech.Percolation


/--
[outC_exitHead_mem_exterior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_exitHead_mem_exterior_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ exitIndex (ω := ω) hfin := by
-- proof
  apply StatMech.Percolation.outC_exitHead_mem_exterior_iff hfin R

/--
[outC_leftExitHead_mem_exterior_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_leftExitHead_mem_exterior_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ leftExitIndex (ω := ω) hfin := by
-- proof
  apply StatMech.Percolation.outC_leftExitHead_mem_exterior_iff hfin R

/--
[outC_clusterBox_ge_exitIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_clusterBox_ge_exitIndex_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  exitIndex (ω := ω) hfin ≤ R := by
-- proof
  apply StatMech.Percolation.outC_clusterBox_ge_exitIndex hfin R hR

/--
[outC_clusterBox_ge_leftExitIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_clusterBox_ge_leftExitIndex_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  leftExitIndex (ω := ω) hfin ≤ R := by
-- proof
  apply StatMech.Percolation.outC_clusterBox_ge_leftExitIndex hfin R hR

/--
[outC_pcFarExitHeadsFar_forces_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_pcFarExitHeadsFar_forces_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : pcFar_ExitHeadsFar ω hfin) :
-- imply
  ∃ R : ℕ, R = exitIndex (ω := ω) hfin ∧ R = leftExitIndex (ω := ω) hfin ∧ cluster 2 ω (origin 2) ⊆ box 2 (exitIndex (ω := ω) hfin) := by
-- proof
  apply StatMech.Percolation.outC_pcFarExitHeadsFar_forces_eq hfin h

/--
[outC_pcFarExitHeadsFar_imp_exitIndex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_pcFarExitHeadsFar_imp_exitIndex_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : pcFar_ExitHeadsFar ω hfin) :
-- imply
  exitIndex (ω := ω) hfin = leftExitIndex (ω := ω) hfin := by
-- proof
  apply StatMech.Percolation.outC_pcFarExitHeadsFar_imp_exitIndex_eq hfin h

/--
[outC_not_pcFarExitHeadsFar_of_exitIndex_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_not_pcFarExitHeadsFar_of_exitIndex_ne_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hne : exitIndex (ω := ω) hfin ≠ leftExitIndex (ω := ω) hfin) :
-- imply
  ¬ pcFar_ExitHeadsFar ω hfin := by
-- proof
  apply StatMech.Percolation.outC_not_pcFarExitHeadsFar_of_exitIndex_ne hfin hne

/--
[outC_farBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_farBox_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R := by
-- proof
  apply StatMech.Percolation.outC_farBox hfin

/--
[outC_axisFarRight_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_axisFarRight_mem_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Percolation.outC_axisFarRight_mem_exterior R

/--
[outC_axisFarLeft_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_axisFarLeft_mem_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Percolation.outC_axisFarLeft_mem_exterior R

/--
[outC_axisFar_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_axisFar_reachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (outC_axisFarRight_mem_exterior R)⟩ ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (outC_axisFarLeft_mem_exterior R)⟩ := by
-- proof
  apply StatMech.Percolation.outC_axisFar_reachable R hR

/--
[outC_axisFarRight_mem_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_axisFarRight_mem_compl_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  (![(R : ℤ) + 1, 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ := by
-- proof
  apply StatMech.Percolation.outC_axisFarRight_mem_compl R hR

/--
[outC_axisFarLeft_mem_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_axisFarLeft_mem_compl_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ := by
-- proof
  apply StatMech.Percolation.outC_axisFarLeft_mem_compl R hR

/--
[outC_farAxisHeadsFar_discharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean)
-/
@[path]
private lemma outC_farAxisHeadsFar_discharge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  outC_FarAxisHeadsFar ω hfin := by
-- proof
  apply StatMech.Percolation.outC_farAxisHeadsFar_discharge hfin


-- created on 2026-10-23
