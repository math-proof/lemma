import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[not_edgeInside_compl_of_edgeInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma not_edgeInside_compl_of_edgeInside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V}
-- given
  (h : edgeInside S e) :
-- imply
  ¬ edgeInside Sᶜ e := by
-- proof
  apply StatMech.Sharpness.not_edgeInside_compl_of_edgeInside G S e h

/--
[restrictTo_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma restrictTo_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
  {e : Sym2 V} :
-- imply
  restrictTo n S e = if edgeInside S e then n e else 0 := by
-- proof
  apply StatMech.Sharpness.restrictTo_apply G n S e

/--
[restrictTo_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma restrictTo_idem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V} :
-- imply
  restrictTo (restrictTo n S) S = restrictTo n S := by
-- proof
  apply StatMech.Sharpness.restrictTo_idem G n S

/--
[restrictTo_add_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma restrictTo_add_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
  {e : Sym2 V}
-- given
  (hn : NoCrossing G n S)
  (he : e ∈ G.edgeFinset) :
-- imply
  n e = restrictTo n S e + restrictTo n Sᶜ e := by
-- proof
  apply StatMech.Sharpness.restrictTo_add_compl G n S hn e he

/--
[restrictTo_left_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma restrictTo_left_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
-- given
  (hn : NoCrossing G n S) :
-- imply
  ∀ e ∈ G.edgeFinset, restrictTo n S e + restrictTo n Sᶜ e = n e := by
-- proof
  apply StatMech.Sharpness.restrictTo_left_inv G n S hn

/--
[weight_restrictTo_mul_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma weight_restrictTo_mul_compl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
  {S : Finset V}
-- given
  (hn : NoCrossing G n S) :
-- imply
  weight G β J n = weight G β J (restrictTo n S) * weight G β J (restrictTo n Sᶜ) := by
-- proof
  apply StatMech.Sharpness.weight_restrictTo_mul_compl G β J n S hn

/--
[incidentFlux_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma incidentFlux_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n m : Current V}
  {x : V} :
-- imply
  incidentFlux G (fun e => n e + m e) x = incidentFlux G n x + incidentFlux G m x := by
-- proof
  apply StatMech.Sharpness.incidentFlux_add G n m x

/--
[sources_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma sources_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n m : Current V} :
-- imply
  sources G (fun e => n e + m e) = sources G n ∆ sources G m := by
-- proof
  apply StatMech.Sharpness.sources_add G n m

/--
[incidentFlux_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma incidentFlux_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
  {x : V}
-- given
  (hn : NoCrossing G n S) :
-- imply
  incidentFlux G n x = incidentFlux G (restrictTo n S) x + incidentFlux G (restrictTo n Sᶜ) x := by
-- proof
  apply StatMech.Sharpness.incidentFlux_split G n S hn x

/--
[incidentFlux_restrictTo_eq_zero_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma incidentFlux_restrictTo_eq_zero_of_notMem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
  {x : V}
-- given
  (hx : x ∉ S) :
-- imply
  incidentFlux G (restrictTo n S) x = 0 := by
-- proof
  apply StatMech.Sharpness.incidentFlux_restrictTo_eq_zero_of_notMem G n S hx

/--
[sources_restrictTo_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma sources_restrictTo_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V} :
-- imply
  sources G (restrictTo n S) ⊆ S := by
-- proof
  apply StatMech.Sharpness.sources_restrictTo_subset G n S

/--
[sources_restrictTo_compl_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma sources_restrictTo_compl_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V} :
-- imply
  sources G (restrictTo n Sᶜ) ⊆ Sᶜ := by
-- proof
  apply StatMech.Sharpness.sources_restrictTo_compl_subset G n S

/--
[sources_restrictTo_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma sources_restrictTo_eq_inter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V}
-- given
  (hn : NoCrossing G n S) :
-- imply
  sources G (restrictTo n S) = sources G n ∩ S ∧ sources G (restrictTo n Sᶜ) = sources G n ∩ Sᶜ := by
-- proof
  apply StatMech.Sharpness.sources_restrictTo_eq_inter G n S hn

/--
[sources_parts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma sources_parts_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {S : Finset V} :
-- imply
  Disjoint (sources G (restrictTo n S)) (sources G (restrictTo n Sᶜ)) := by
-- proof
  apply StatMech.Sharpness.sources_parts_disjoint G n S

/--
[current_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean)
-/
@[path]
private lemma current_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n : Current V}
  {S : Finset V}
-- given
  (hn : NoCrossing G n S) :
-- imply
  (∀ e ∈ G.edgeFinset, restrictTo n S e + restrictTo n Sᶜ e = n e) ∧ weight G β J n = weight G β J (restrictTo n S) * weight G β J (restrictTo n Sᶜ) ∧ sources G n = sources G (restrictTo n S) ∪ sources G (restrictTo n Sᶜ) ∧ sources G (restrictTo n S) = sources G n ∩ S ∧ sources G (restrictTo n Sᶜ) = sources G n ∩ Sᶜ := by
-- proof
  apply StatMech.Sharpness.current_split G β J n S hn


-- created on 2026-10-23
