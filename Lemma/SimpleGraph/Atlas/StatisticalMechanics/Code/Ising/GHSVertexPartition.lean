import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
open Finset Classical StatMech StatMech.Ising


/--
[ghsvp_wJ_zero_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_wJ_zero_factor_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {s : ConfigSpace W}
-- given
  (J : Sym2 W -> Real) :
-- imply
  wJ E J (fun _ => 0) s = ∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e)) := by
-- proof
  apply StatMech.Ising.ghsvp_wJ_zero_factor E J s

/--
[ghsvp_wJ_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_wJ_factor_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {s : ConfigSpace W}
-- given
  (J : Sym2 W -> Real)
  (hf : W -> Real) :
-- imply
  wJ E J hf s = (∏ e ∈ E, (Real.cosh (J e) + bond s e * Real.sinh (J e))) * ∏ x : W, (Real.cosh (hf x) + spin s x * Real.sinh (hf x)) := by
-- proof
  apply StatMech.Ising.ghsvp_wJ_factor E J hf s

/--
[ghsvp_expJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_expJ_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {A : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hf : W -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x) :
-- imply
  0 <= expJ E J hf (spinProd A) := by
-- proof
  apply StatMech.Ising.ghsvp_expJ_nonneg E J hf hJ hhf A

/--
[ghsvp_expJ_zero_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_expJ_zero_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {A : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e) :
-- imply
  0 <= expJ E J (fun _ => 0) (spinProd A) := by
-- proof
  apply StatMech.Ising.ghsvp_expJ_zero_nonneg E J hJ A

/--
[ghsvp_ZJ_zero_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_ZJ_zero_mono_eq
  [Fintype W]
  [DecidableEq W]
  {E F : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (hJ : forall e, 0 <= J e)
  (hEF : E ⊆ F)
  (hnd : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  ZJ E J (fun _ => 0) <= ZJ F J (fun _ => 0) := by
-- proof
  apply StatMech.Ising.ghsvp_ZJ_zero_mono J hJ E F hEF hnd

/--
[ghsvp_ZJ_zero_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_ZJ_zero_logSupermodular_eq
  [Fintype W]
  [DecidableEq W]
  {E F : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (hJ : forall e, 0 <= J e)
  (hnd : ∀ e ∈ E ∪ F, ¬ e.IsDiag) :
-- imply
  ZJ E J (fun _ => 0) * ZJ F J (fun _ => 0) <= ZJ (E ∪ F) J (fun _ => 0) * ZJ (E ∩ F) J (fun _ => 0) := by
-- proof
  apply StatMech.Ising.ghsvp_ZJ_zero_logSupermodular J hJ E F hnd

/--
[ghsvp_vertexEdges_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexEdges_mono_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)} :
-- imply
  Monotone (ghsvp_vertexEdges E) := by
-- proof
  apply StatMech.Ising.ghsvp_vertexEdges_mono E

/--
[ghsvp_vertexEdges_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexEdges_inter_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S T : Finset W} :
-- imply
  ghsvp_vertexEdges E (S ∩ T) = ghsvp_vertexEdges E S ∩ ghsvp_vertexEdges E T := by
-- proof
  apply StatMech.Ising.ghsvp_vertexEdges_inter E S T

/--
[ghsvp_vertexEdges_union_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexEdges_union_subset_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S T : Finset W} :
-- imply
  ghsvp_vertexEdges E S ∪ ghsvp_vertexEdges E T ⊆ ghsvp_vertexEdges E (S ∪ T) := by
-- proof
  apply StatMech.Ising.ghsvp_vertexEdges_union_subset E S T

/--
[ghsvp_vertexZ_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexZ_logSupermodular_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S T : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hJ : forall e, 0 <= J e)
  (hnd : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  ghsvp_vertexZ E J S * ghsvp_vertexZ E J T <= ghsvp_vertexZ E J (S ∪ T) * ghsvp_vertexZ E J (S ∩ T) := by
-- proof
  apply StatMech.Ising.ghsvp_vertexZ_logSupermodular E J hJ hnd S T

/--
[ghsvp_vertexCorr_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexCorr_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S P : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hJ : ∀ e, 0 <= J e) :
-- imply
  0 <= ghsvp_vertexCorr E J S P := by
-- proof
  apply StatMech.Ising.ghsvp_vertexCorr_nonneg E J hJ S P

/--
[ghsvp_vertexCorr_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexCorr_mono_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S T : Finset W}
  {P : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hJ : ∀ e, 0 <= J e)
  (hnd : ∀ e ∈ E, ¬ e.IsDiag)
  (hST : S ⊆ T) :
-- imply
  ghsvp_vertexCorr E J S P <= ghsvp_vertexCorr E J T P := by
-- proof
  apply StatMech.Ising.ghsvp_vertexCorr_mono E J hJ hnd hST P

/--
[ghsvp_vertexCorrField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexCorrField_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S P : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hf : W -> Real)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x) :
-- imply
  0 <= ghsvp_vertexCorrField E J hf S P := by
-- proof
  apply StatMech.Ising.ghsvp_vertexCorrField_nonneg E J hf hJ hhf S P

/--
[ghsvp_vertexCorrField_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexCorrField_mono_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S T : Finset W}
  {P : Finset W}
-- given
  (J : Sym2 W -> Real)
  (hf : W -> Real)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hnd : ∀ e ∈ E, ¬ e.IsDiag)
  (hST : S ⊆ T) :
-- imply
  ghsvp_vertexCorrField E J hf S P <= ghsvp_vertexCorrField E J hf T P := by
-- proof
  apply StatMech.Ising.ghsvp_vertexCorrField_mono E J hf hJ hhf hnd hST P

/--
[ghsvp_wJ_mergeConfig_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_wJ_mergeConfig_independent_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S : Finset W}
-- given
  (J : Sym2 W -> Real)
  (a : ↑S -> Bool)
  (b c : ({v : W // v ∉ S}) -> Bool) :
-- imply
  wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a b) = wJ (ghsvp_vertexEdges E S) J (fun _ => 0) (ghsvp_mergeConfig S a c) := by
-- proof
  apply StatMech.Ising.ghsvp_wJ_mergeConfig_independent E J S a b c

/--
[ghsvp_inactiveConfig_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_inactiveConfig_card_eq
  [Fintype W]
  [DecidableEq W]
  {S : Finset W} :
-- imply
  Fintype.card (({v : W // v ∉ S}) -> Bool) = 2 ^ (Fintype.card W - S.card) := by
-- proof
  apply StatMech.Ising.ghsvp_inactiveConfig_card S

/--
[ghsvp_vertexZ_eq_inactiveCard_mul_activeZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexZ_eq_inactiveCard_mul_activeZ_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {S : Finset W}
-- given
  (J : Sym2 W -> Real) :
-- imply
  ghsvp_vertexZ E J S = Fintype.card (({v : W // v ∉ S}) -> Bool) * ghsvp_activeZ E J S := by
-- proof
  apply StatMech.Ising.ghsvp_vertexZ_eq_inactiveCard_mul_activeZ E J S

/--
[ghsvp_someSet_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_someSet_mono_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V] :
-- imply
  Monotone (ghsvp_someSet : Finset V -> Finset (Option V)) := by
-- proof
  apply StatMech.Ising.ghsvp_someSet_mono

/--
[ghsvp_someSet_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_someSet_inter_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A B : Finset V} :
-- imply
  ghsvp_someSet (A ∩ B) = ghsvp_someSet A ∩ ghsvp_someSet B := by
-- proof
  apply StatMech.Ising.ghsvp_someSet_inter A B

/--
[ghsvp_someSet_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_someSet_union_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A B : Finset V} :
-- imply
  ghsvp_someSet (A ∪ B) = ghsvp_someSet A ∪ ghsvp_someSet B := by
-- proof
  apply StatMech.Ising.ghsvp_someSet_union A B

/--
[ghsvp_fieldSet_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_fieldSet_inter_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A B : Finset V} :
-- imply
  ghsvp_fieldSet (A ∩ B) = ghsvp_fieldSet A ∩ ghsvp_fieldSet B := by
-- proof
  apply StatMech.Ising.ghsvp_fieldSet_inter A B

/--
[ghsvp_fieldSet_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_fieldSet_union_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A B : Finset V} :
-- imply
  ghsvp_fieldSet (A ∪ B) = ghsvp_fieldSet A ∪ ghsvp_fieldSet B := by
-- proof
  apply StatMech.Ising.ghsvp_fieldSet_union A B

/--
[ghsvp_edgeInside_map_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_edgeInside_map_some_iff_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A : Finset V}
  {e : Sym2 V} :
-- imply
  Sharpness.edgeInside (ghsvp_fieldSet A) (Sym2.map some e) ↔ Sharpness.edgeInside A e := by
-- proof
  apply StatMech.Ising.ghsvp_edgeInside_map_some_iff A e

/--
[ghsvp_origEdges_filter_fieldSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_origEdges_filter_fieldSet_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V} :
-- imply
  (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) = (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
-- proof
  apply StatMech.Ising.ghsvp_origEdges_filter_fieldSet G A

/--
[ghsvp_ghostEdges_filter_fieldSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_ghostEdges_filter_fieldSet_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A : Finset V} :
-- imply
  (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_fieldSet A)) = A.image (fun x => s(some x, none)) := by
-- proof
  apply StatMech.Ising.ghsvp_ghostEdges_filter_fieldSet A

/--
[ghsvp_fieldSet_couplingSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_fieldSet_couplingSum_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (β h : Real) :
-- imply
  (∑ e ∈ ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A), ghostCoupling (2 * β * h) 1 (fun _ => 2 * β) e * bond s e) = (∑ e ∈ ghsvp_vertexEdges G.edgeFinset A, (2 * β) * bond (fun x => s (some x)) e) + (2 * β * h) * spin s none * ∑ x ∈ A, spin s (some x) := by
-- proof
  apply StatMech.Ising.ghsvp_fieldSet_couplingSum G β h A s

/--
[ghsvp_fieldSet_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_fieldSet_weight_eq_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (β h : Real) :
-- imply
  wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_fieldSet A)) (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s = wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun x => if x ∈ A then (2 * β * h) * spin s none else 0) (fun x => s (some x)) := by
-- proof
  apply StatMech.Ising.ghsvp_fieldSet_weight_eq G β h A s

/--
[ghsvp_edgeInside_map_someSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_edgeInside_map_someSet_iff_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A : Finset V}
  {e : Sym2 V} :
-- imply
  Sharpness.edgeInside (ghsvp_someSet A) (Sym2.map some e) ↔ Sharpness.edgeInside A e := by
-- proof
  apply StatMech.Ising.ghsvp_edgeInside_map_someSet_iff A e

/--
[ghsvp_origEdges_filter_someSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_origEdges_filter_someSet_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V} :
-- imply
  (FieldGhostDict.origEdges G).filter (Sharpness.edgeInside (ghsvp_someSet A)) = (ghsvp_vertexEdges G.edgeFinset A).image (Sym2.map some) := by
-- proof
  apply StatMech.Ising.ghsvp_origEdges_filter_someSet G A

/--
[ghsvp_ghostEdges_filter_someSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_ghostEdges_filter_someSet_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {A : Finset V} :
-- imply
  (FieldGhostDict.ghostEdges V).filter (Sharpness.edgeInside (ghsvp_someSet A)) = ∅ := by
-- proof
  apply StatMech.Ising.ghsvp_ghostEdges_filter_someSet A

/--
[ghsvp_someSet_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_someSet_weight_eq_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {s : ConfigSpace (Option V)}
-- given
  (β h : Real) :
-- imply
  wJ (ghsvp_vertexEdges (withGhost G).edgeFinset (ghsvp_someSet A)) (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (fun _ => 0) s = wJ (ghsvp_vertexEdges G.edgeFinset A) (fun _ => 2 * β) (fun _ => 0) (fun x => s (some x)) := by
-- proof
  apply StatMech.Ising.ghsvp_someSet_weight_eq G β h A s

/--
[ghsvp_wJ_negField_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_wJ_negField_flip_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  wJ E J (fun x => -hf x) (FieldGhostDict.flipV s) = wJ E J hf s := by
-- proof
  apply StatMech.Ising.ghsvp_wJ_negField_flip E J hf s

/--
[ghsvp_ZJ_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_ZJ_negField_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ZJ E J (fun x => -hf x) = ZJ E J hf := by
-- proof
  apply StatMech.Ising.ghsvp_ZJ_negField E J hf

/--
[ghsvp_vertexZ_fieldSet_eq_two_mul_tZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexZ_fieldSet_eq_two_mul_tZ_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : Real) :
-- imply
  ghsvp_vertexZ (withGhost G).edgeFinset (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_fieldSet A) = 2 * ghsvp_tZ G β h A := by
-- proof
  apply StatMech.Ising.ghsvp_vertexZ_fieldSet_eq_two_mul_tZ G β h A

/--
[ghsvp_vertexZ_someSet_eq_two_mul_uZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_vertexZ_someSet_eq_two_mul_uZ_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : Real) :
-- imply
  ghsvp_vertexZ (withGhost G).edgeFinset (ghostCoupling (2 * β * h) 1 (fun _ => 2 * β)) (ghsvp_someSet A) = 2 * ghsvp_uZ G β A := by
-- proof
  apply StatMech.Ising.ghsvp_vertexZ_someSet_eq_two_mul_uZ G β h A

/--
[ghsvp_subsetMass_eq_four_mul_tZ_uZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_subsetMass_eq_four_mul_tZ_uZ_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : Real) :
-- imply
  ghsvp_subsetMass G β h A = 4 * (ghsvp_tZ G β h A * ghsvp_uZ G β Aᶜ) := by
-- proof
  apply StatMech.Ising.ghsvp_subsetMass_eq_four_mul_tZ_uZ G β h A

/--
[ghsvp_subsetMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_subsetMass_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (β h : Real) :
-- imply
  0 <= ghsvp_subsetMass G β h A := by
-- proof
  apply StatMech.Ising.ghsvp_subsetMass_nonneg G β h A

/--
[ghsvp_subsetMass_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_subsetMass_logSupermodular_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (β h : Real)
  (hβ : 0 <= β)
  (hh : 0 <= h) :
-- imply
  ghsvp_subsetMass G β h A * ghsvp_subsetMass G β h B <= ghsvp_subsetMass G β h (A ∪ B) * ghsvp_subsetMass G β h (A ∩ B) := by
-- proof
  apply StatMech.Ising.ghsvp_subsetMass_logSupermodular G β h hβ hh A B

/--
[ghsvp_disagreementCorr_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_disagreementCorr_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : Real}
  {o x : V}
  {A : Finset V}
-- given
  (hβ : 0 <= β) :
-- imply
  0 <= ghsvp_disagreementCorr G β o x A := by
-- proof
  apply StatMech.Ising.ghsvp_disagreementCorr_nonneg G β hβ o x A

/--
[ghsvp_disagreementCorr_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_disagreementCorr_antitone_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : Real}
  {o x : V}
-- given
  (hβ : 0 <= β) :
-- imply
  Antitone (ghsvp_disagreementCorr G β o x) := by
-- proof
  apply StatMech.Ising.ghsvp_disagreementCorr_antitone G β hβ o x

/--
[ghsvp_agreementMag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_agreementMag_nonneg_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
  {A : Finset V}
-- given
  (β h : Real)
  (hβ : 0 <= β)
  (hh : 0 <= h) :
-- imply
  0 <= ghsvp_agreementMag G β h y A := by
-- proof
  apply StatMech.Ising.ghsvp_agreementMag_nonneg G β h hβ hh y A

/--
[ghsvp_agreementMag_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean)
-/
@[path]
private lemma ghsvp_agreementMag_monotone_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {y : V}
-- given
  (β h : Real)
  (hβ : 0 <= β)
  (hh : 0 <= h) :
-- imply
  Monotone (ghsvp_agreementMag G β h y) := by
-- proof
  apply StatMech.Ising.ghsvp_agreementMag_monotone G β h hβ hh y


-- created on 2026-10-23
