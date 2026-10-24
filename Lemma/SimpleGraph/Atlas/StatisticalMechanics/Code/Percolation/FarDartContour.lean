import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.FarDartContour
open Finset Set SimpleGraph Function StatMech StatMech.Percolation


/--
[fdc_rightExitIdx_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightExitIdx_le_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  fdc_rightExitIdx (ω := ω) hfin R ≤ R := by
-- proof
  apply StatMech.Percolation.fdc_rightExitIdx_le hfin R

/--
[fdc_rightExitIdx_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightExitIdx_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  axisSite (fdc_rightExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_rightExitIdx_mem hfin R

/--
[fdc_rightExitIdx_is_greatest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightExitIdx_is_greatest_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
  {k : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h0 : fdc_rightExitIdx (ω := ω) hfin R < k)
  (h1 : k ≤ R) :
-- imply
  axisSite k ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_rightExitIdx_is_greatest hfin R h0 h1

/--
[fdc_rightExitIdx_succ_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightExitIdx_succ_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_rightExitIdx_succ_not_mem hfin R hR

/--
[fdc_axis_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_axis_reach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a j : ℕ}
-- given
  (hout : ∀ k, a ≤ k → k ≤ a + j → (axisSite k : Site 2) ∉ K) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨axisSite a, hout a le_rfl (by omega)⟩ ⟨axisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
-- proof
  apply StatMech.Percolation.fdc_axis_reach K a j hout

/--
[fdc_rightExit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightExit_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (axisSite (fdc_rightExitIdx (ω := ω) hfin R)) (axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1)) := by
-- proof
  apply StatMech.Percolation.fdc_rightExit_adj hfin R

/--
[fdc_farExitDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitDart_tail_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (fdc_farExitDart (ω := ω) hfin R).tail = axisSite (fdc_rightExitIdx (ω := ω) hfin R) := by
-- proof
  apply StatMech.Percolation.fdc_farExitDart_tail hfin R

/--
[fdc_farExitDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitDart_head_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (fdc_farExitDart (ω := ω) hfin R).head = axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) := by
-- proof
  apply StatMech.Percolation.fdc_farExitDart_head hfin R

/--
[fdc_farExitDart_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitDart_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farExitDart (ω := ω) hfin R) := by
-- proof
  apply StatMech.Percolation.fdc_farExitDart_isBoundaryDart hfin R hR

/--
[fdc_rightRun_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_rightRun_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
  {k : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (h0 : fdc_rightExitIdx (ω := ω) hfin R + 1 ≤ k)
  (h1 : k ≤ R + 1) :
-- imply
  (axisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_rightRun_not_mem hfin R hR h0 h1

/--
[fdc_farExitDart_head_reaches_axisFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitDart_head_reaches_axisFar_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(fdc_farExitDart (ω := ω) hfin R).head, (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ ⟨axisSite (R + 1), fdc_rightRun_not_mem (ω := ω) hfin R hR (Nat.succ_le_succ (fdc_rightExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
-- proof
  apply StatMech.Percolation.fdc_farExitDart_head_reaches_axisFar hfin R hR

/--
[fdc_leftExitIdx_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftExitIdx_le_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  fdc_leftExitIdx (ω := ω) hfin R ≤ R := by
-- proof
  apply StatMech.Percolation.fdc_leftExitIdx_le hfin R

/--
[fdc_leftExitIdx_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftExitIdx_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_leftExitIdx_mem hfin R

/--
[fdc_leftExitIdx_is_greatest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftExitIdx_is_greatest_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
  {k : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h0 : fdc_leftExitIdx (ω := ω) hfin R < k)
  (h1 : k ≤ R) :
-- imply
  leftAxisSite k ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_leftExitIdx_is_greatest hfin R h0 h1

/--
[fdc_leftRun_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftRun_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
  {k : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (h0 : fdc_leftExitIdx (ω := ω) hfin R + 1 ≤ k)
  (h1 : k ≤ R + 1) :
-- imply
  (leftAxisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_leftRun_not_mem hfin R hR h0 h1

/--
[fdc_leftExitIdx_succ_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftExitIdx_succ_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Percolation.fdc_leftExitIdx_succ_not_mem hfin R hR

/--
[fdc_leftExit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftExit_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R)) (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1)) := by
-- proof
  apply StatMech.Percolation.fdc_leftExit_adj hfin R

/--
[fdc_farLeftExitDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farLeftExitDart_tail_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (fdc_farLeftExitDart (ω := ω) hfin R).tail = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) := by
-- proof
  apply StatMech.Percolation.fdc_farLeftExitDart_tail hfin R

/--
[fdc_farLeftExitDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farLeftExitDart_head_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (fdc_farLeftExitDart (ω := ω) hfin R).head = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) := by
-- proof
  apply StatMech.Percolation.fdc_farLeftExitDart_head hfin R

/--
[fdc_farLeftExitDart_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farLeftExitDart_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farLeftExitDart (ω := ω) hfin R) := by
-- proof
  apply StatMech.Percolation.fdc_farLeftExitDart_isBoundaryDart hfin R hR

/--
[fdc_leftAxis_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftAxis_reach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a j : ℕ}
-- given
  (hout : ∀ k, a ≤ k → k ≤ a + j → (leftAxisSite k : Site 2) ∉ K) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨leftAxisSite a, hout a le_rfl (by omega)⟩ ⟨leftAxisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
-- proof
  apply StatMech.Percolation.fdc_leftAxis_reach K a j hout

/--
[fdc_farLeftExitDart_head_reaches_axisFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farLeftExitDart_head_reaches_axisFar_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head, (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ ⟨leftAxisSite (R + 1), fdc_leftRun_not_mem (ω := ω) hfin R hR (Nat.succ_le_succ (fdc_leftExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
-- proof
  apply StatMech.Percolation.fdc_farLeftExitDart_head_reaches_axisFar hfin R hR

/--
[fdc_axisSite_eq_farRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_axisSite_eq_farRight_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (axisSite (R + 1) : Site 2) = ![(R : ℤ) + 1, 0] := by
-- proof
  apply StatMech.Percolation.fdc_axisSite_eq_farRight R

/--
[fdc_leftAxisSite_eq_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_leftAxisSite_eq_farLeft_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (leftAxisSite (R + 1) : Site 2) = ![-((R : ℤ) + 1), 0] := by
-- proof
  apply StatMech.Percolation.fdc_leftAxisSite_eq_farLeft R

/--
[fdc_farExitHeads_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitHeads_sameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(fdc_farExitDart (ω := ω) hfin R).head, (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head, (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ := by
-- proof
  apply StatMech.Percolation.fdc_farExitHeads_sameComponent hfin R hR

/--
[fdc_farExitHeads_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitHeads_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  outC_FarAxisHeadsFar ω hfin := by
-- proof
  apply StatMech.Percolation.fdc_farExitHeads_exterior hfin

/--
[fdc_farExitDartsSameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_farExitDartsSameOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ∃ n : ℕ, (dartNext (cluster 2 ω (origin 2)))^[n] (fdc_farExitDart (ω := ω) hfin R) = fdc_farLeftExitDart (ω := ω) hfin R := by
-- proof
  apply StatMech.Percolation.fdc_farExitDartsSameOrbit hfin hInt R hR

/--
[fdc_sameOrbit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_sameOrbit_symm_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hn : (dartNext K)^[n] e = f) :
-- imply
  ∃ m : ℕ, (dartNext K)^[m] f = e := by
-- proof
  apply StatMech.Percolation.fdc_sameOrbit_symm K hK e f he hn

/--
[fdc_sameOrbit_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_sameOrbit_trans_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f g : Dart}
  {a b : ℕ}
-- given
  (ha : (dartNext K)^[a] e = f)
  (hb : (dartNext K)^[b] f = g) :
-- imply
  ∃ c : ℕ, (dartNext K)^[c] e = g := by
-- proof
  apply StatMech.Percolation.fdc_sameOrbit_trans K e f g ha hb

/--
[fdc_exitDartsSameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_exitDartsSameOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hre : fdc_FarReanchors ω hfin R) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Percolation.fdc_exitDartsSameOrbit hfin hInt R hR hre

/--
[fdc_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean)
-/
@[path]
private lemma fdc_pc_lt_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧ ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R ∧ fdc_FarReanchors ω hfin R) :
-- imply
  (StatMech.Percolation.pc 2 : ℝ) < 1 := by
-- proof
  apply StatMech.Percolation.fdc_pc_lt_one h


-- created on 2026-10-23
