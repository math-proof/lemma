import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part5
open Finset Classical StatMech StatMech.FrontierA


/--
[connK_sdiff_or_meets_edgeConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma connK_sdiff_or_meets_edgeConnected_eq
  [Fintype ι]
  [DecidableEq ι]
  {H X : Finset ι}
  {i k v : V}
-- given
  (ends : ι -> Sym2 V)
  (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
  (hiv : connK ends H i v) :
-- imply
  connK ends (H \ X) i v ∨ ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
-- proof
  apply StatMech.FrontierA.connK_sdiff_or_meets_edgeConnected ends H X i k v hXconn hiv

/--
[exists_connK_sdiff_meets_of_edgeConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma exists_connK_sdiff_meets_of_edgeConnected_eq
  [Fintype ι]
  [DecidableEq ι]
  {H X : Finset ι}
  {i k : V}
-- given
  (ends : ι -> Sym2 V)
  (hXconn : ∀ e ∈ X, ∀ x ∈ ends e, connK ends X k x)
  (hik : connK ends H i k) :
-- imply
  ∃ y, connK ends (H \ X) i y ∧ connK ends X k y := by
-- proof
  apply StatMech.FrontierA.exists_connK_sdiff_meets_of_edgeConnected ends H X i k hXconn hik

/--
[edgeComponent_subset_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma edgeComponent_subset_edges_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {k : V}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  edgeComponent ends K k ⊆ K := by
-- proof
  apply StatMech.FrontierA.edgeComponent_subset_edges ends K k

/--
[connK_edgeComponent_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma connK_edgeComponent_of_conn_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {k x : V}
-- given
  (ends : ι -> Sym2 V)
  (hkx : connK ends K k x) :
-- imply
  connK ends (edgeComponent ends K k) k x := by
-- proof
  apply StatMech.FrontierA.connK_edgeComponent_of_conn ends K k x hkx

/--
[edgeComponent_endpoint_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma edgeComponent_endpoint_connK_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {k : V}
-- given
  (ends : ι -> Sym2 V) :
-- imply
  ∀ e ∈ edgeComponent ends K k, ∀ x ∈ ends e, connK ends (edgeComponent ends K k) k x := by
-- proof
  apply StatMech.FrontierA.edgeComponent_endpoint_connK ends K k

/--
[finiteTreeMiddleTransfer_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeMiddleTransfer_spec_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
-- imply
  FiniteTreeMiddleTransferWitness ends U k l c (finiteTreeMiddleTransfer ends U k l c) := by
-- proof
  apply StatMech.FrontierA.finiteTreeMiddleTransfer_spec ends U k l c h

/--
[finiteTreeMiddleUnion_middleSwapOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeMiddleUnion_middleSwapOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {U X : Finset ι}
-- given
  (c : ↑U -> Fin 4)
  (hX : X ⊆ finiteTreeMiddleUnion U c) :
-- imply
  finiteTreeMiddleUnion U (middleSwapOn U X c) = finiteTreeMiddleUnion U c := by
-- proof
  apply StatMech.FrontierA.finiteTreeMiddleUnion_middleSwapOn U X c hX

/--
[finiteTreeMiddleTransferWitness_middleSwapOn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeMiddleTransferWitness_middleSwapOn_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {U X Y : Finset ι}
  {k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hX : X ⊆ finiteTreeMiddleUnion U c) :
-- imply
  FiniteTreeMiddleTransferWitness ends U k l (middleSwapOn U X c) Y ↔ FiniteTreeMiddleTransferWitness ends U k l c Y := by
-- proof
  apply StatMech.FrontierA.finiteTreeMiddleTransferWitness_middleSwapOn_iff ends U X Y k l c hX

/--
[finiteTreeMiddleTransfer_selected_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeMiddleTransfer_selected_invariant_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
-- imply
  finiteTreeMiddleTransfer ends U k l (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) = finiteTreeMiddleTransfer ends U k l c := by
-- proof
  apply StatMech.FrontierA.finiteTreeMiddleTransfer_selected_invariant ends U k l c h

/--
[exists_finiteTreeMiddleTransferWitness_of_mixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma exists_finiteTreeMiddleTransferWitness_of_mixed_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X := by
-- proof
  apply StatMech.FrontierA.exists_finiteTreeMiddleTransferWitness_of_mixed ends U c hloop hkl hmix

/--
[finiteTreeSourceComponentTransfer_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeSourceComponentTransfer_spec_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  finiteTreeSourceComponentTransfer ends U k c ⊆ finiteTreeMiddleUnion U c ∧ sources ends (finiteTreeSourceComponentTransfer ends U k c) = {k, l} ∧ (∀ e ∈ finiteTreeSourceComponentTransfer ends U k c, ∀ x ∈ ends e, connK ends (finiteTreeSourceComponentTransfer ends U k c) k x) := by
-- proof
  apply StatMech.FrontierA.finiteTreeSourceComponentTransfer_spec ends U c hloop hkl hmix

/--
[finiteTree_sourceComponentSwitch_separatedSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_sourceComponentSwitch_separatedSources_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  FiniteTreeSeparatedSources ends U i j k l (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) := by
-- proof
  apply StatMech.FrontierA.finiteTree_sourceComponentSwitch_separatedSources ends U c hloop hkl hmix

/--
[finiteTree_sourceComponentSwitch_hasCommonVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_sourceComponentSwitch_hasCommonVertex_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  ∃ y, connK ends (colorClass U (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) 0 ∪ colorClass U (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) 1) i y ∧ connK ends (colorClass U (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) 2 ∪ colorClass U (middleSwapOn U (finiteTreeSourceComponentTransfer ends U k c) c) 3) k y := by
-- proof
  apply StatMech.FrontierA.finiteTree_sourceComponentSwitch_hasCommonVertex ends U c hloop hkl hmix

/--
[finiteTreeInvariantComponentTransfer_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeInvariantComponentTransfer_spec_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  finiteTreeInvariantComponentTransfer ends U k c ⊆ finiteTreeMiddleUnion U c ∧ sources ends (finiteTreeInvariantComponentTransfer ends U k c) = {k, l} ∧ (∀ e ∈ finiteTreeInvariantComponentTransfer ends U k c, ∀ x ∈ ends e, connK ends (finiteTreeInvariantComponentTransfer ends U k c) k x) := by
-- proof
  apply StatMech.FrontierA.finiteTreeInvariantComponentTransfer_spec ends U c hloop hkl hmix

/--
[finiteTreeInvariantComponentTransfer_selected_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTreeInvariantComponentTransfer_selected_invariant_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {k : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hsub : finiteTreeInvariantComponentTransfer ends U k c ⊆ finiteTreeMiddleUnion U c) :
-- imply
  finiteTreeInvariantComponentTransfer ends U k (middleSwapOn U (finiteTreeInvariantComponentTransfer ends U k c) c) = finiteTreeInvariantComponentTransfer ends U k c := by
-- proof
  apply StatMech.FrontierA.finiteTreeInvariantComponentTransfer_selected_invariant ends U k c hsub

/--
[finiteTree_invariantComponentSwitch_separatedSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_invariantComponentSwitch_separatedSources_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  FiniteTreeSeparatedSources ends U i j k l (middleSwapOn U (finiteTreeInvariantComponentTransfer ends U k c) c) := by
-- proof
  apply StatMech.FrontierA.finiteTree_invariantComponentSwitch_separatedSources ends U c hloop hkl hmix

/--
[finiteTree_invariantComponentSwitch_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_invariantComponentSwitch_involutive_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  middleSwapOn U (finiteTreeInvariantComponentTransfer ends U k (middleSwapOn U (finiteTreeInvariantComponentTransfer ends U k c) c)) (middleSwapOn U (finiteTreeInvariantComponentTransfer ends U k c) c) = c := by
-- proof
  apply StatMech.FrontierA.finiteTree_invariantComponentSwitch_involutive ends U c hloop hkl hmix

/--
[finiteTree_selectedSwitch_separatedSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_selectedSwitch_separatedSources_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {i j k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (hloop : ∀ e ∈ U, ¬(ends e).IsDiag)
  (hkl : k ≠ l)
  (hmix : FiniteTreeMixedPattern ends U i j k l c) :
-- imply
  FiniteTreeSeparatedSources ends U i j k l (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) := by
-- proof
  apply StatMech.FrontierA.finiteTree_selectedSwitch_separatedSources ends U c hloop hkl hmix

/--
[finiteTree_selectedSwitch_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorSwitch.lean)
-/
@[path]
private lemma finiteTree_selectedSwitch_involutive_eq
  [Fintype ι]
  [DecidableEq ι]
  {U : Finset ι}
  {k l : V}
-- given
  (ends : ι -> Sym2 V)
  (c : ↑U -> Fin 4)
  (h : ∃ X, FiniteTreeMiddleTransferWitness ends U k l c X) :
-- imply
  middleSwapOn U (finiteTreeMiddleTransfer ends U k l (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c)) (middleSwapOn U (finiteTreeMiddleTransfer ends U k l c) c) = c := by
-- proof
  apply StatMech.FrontierA.finiteTree_selectedSwitch_involutive ends U k l c h


-- created on 2026-10-23
