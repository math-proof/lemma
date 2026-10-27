import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[ocd_innerEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerEdge_injective_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
-- given
  (hι : Function.Injective ιV) :
-- imply
  Function.Injective (ocd_innerEdge ιV) := by
-- proof
  apply StatMech.FK.ocd_innerEdge_injective Gin Gout ιV hι

/--
[ocd_innerEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerEdge_mk_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {x y : Vin} :
-- imply
  ocd_innerEdge ιV s(x, y) = s(ιV x, ιV y) := by
-- proof
  apply StatMech.FK.ocd_innerEdge_mk Gin Gout ιV x y

/--
[ocd_isInnerVert_iff_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_isInnerVert_iff_range_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {v : Vout} :
-- imply
  ocd_IsInnerVert ιV v ↔ ∃ x, ιV x = v := by
-- proof
  apply StatMech.FK.ocd_isInnerVert_iff_range Gin Gout ιV v

/--
[ocd_mem_innerEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_mem_innerEdgeFinset_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {e : Sym2 Vout} :
-- imply
  e ∈ ocd_innerEdgeFinset (Vin := Vin) ιV ↔ e ∈ Set.range (ocd_innerEdge ιV) := by
-- proof
  apply StatMech.FK.ocd_mem_innerEdgeFinset Gin Gout ιV

/--
[ocd_psiExt_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiExt_innerEdge_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
  {e : Sym2 Vin}
-- given
  (hι : Function.Injective ιV) :
-- imply
  ocd_psiExt ιV ψ ω (ocd_innerEdge ιV e) = ω e := by
-- proof
  apply StatMech.FK.ocd_psiExt_innerEdge Gin Gout ιV hι ψ ω e

/--
[ocd_psiExt_eq_psi_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiExt_eq_psi_of_not_range_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
  {e : Sym2 Vout}
-- given
  (he : e ∉ Set.range (ocd_innerEdge ιV)) :
-- imply
  ocd_psiExt ιV ψ ω e = ψ e := by
-- proof
  apply StatMech.FK.ocd_psiExt_eq_psi_of_not_range Gin Gout ιV ψ ω he

/--
[ocd_psiExt_innerEdge_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiExt_innerEdge_pair_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
  {x y : Vin}
-- given
  (hι : Function.Injective ιV) :
-- imply
  ocd_psiExt ιV ψ ω s(ιV x, ιV y) = ω s(x, y) := by
-- proof
  apply StatMech.FK.ocd_psiExt_innerEdge_pair Gin Gout ιV hι ψ ω x y

/--
[ocd_innerRestrict_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerRestrict_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
-- given
  (hι : Function.Injective ιV) :
-- imply
  ocd_innerRestrict ιV (ocd_psiExt ιV ψ ω) = ω := by
-- proof
  apply StatMech.FK.ocd_innerRestrict_psiExt Gin Gout ιV hι ψ ω

/--
[ocd_agreesOff_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_agreesOff_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)} :
-- imply
  AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω) := by
-- proof
  apply StatMech.FK.ocd_agreesOff_psiExt Gin Gout ιV ψ ω

/--
[ocd_psiExt_innerRestrict_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiExt_innerRestrict_of_agreesOff_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ ρ : ConfigSpace (Sym2 Vout)}
-- given
  (hι : Function.Injective ιV)
  (hρ : AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) :
-- imply
  ocd_psiExt ιV ψ (ocd_innerRestrict ιV ρ) = ρ := by
-- proof
  apply StatMech.FK.ocd_psiExt_innerRestrict_of_agreesOff Gin Gout ιV hι hρ

/--
[ocd_condFibre_eq_image_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condFibre_eq_image_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (hι : Function.Injective ιV) :
-- imply
  condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ = Finset.univ.image (ocd_psiExt ιV ψ) := by
-- proof
  apply StatMech.FK.ocd_condFibre_eq_image_psiExt Gin Gout ιV hι ψ

/--
[ocd_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outsideGraph_adj_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vout}
-- given
  (bdryOut : Vout → Prop) :
-- imply
  (ocd_outsideGraph Gout ιV bdryOut ψ).Adj x y ↔ (Gout.Adj x y ∧ ψ s(x, y) = true ∧ s(x, y) ∉ Set.range (ocd_innerEdge ιV)) ∨ (x ≠ y ∧ bdryOut x ∧ bdryOut y) := by
-- proof
  apply StatMech.FK.ocd_outsideGraph_adj Gin Gout ιV bdryOut ψ x y

/--
[ocd_inducedWiring_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_inducedWiring_adj_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop) :
-- imply
  (ocd_inducedWiring Gout ιV bdryOut ψ).Adj x y ↔ x ≠ y ∧ (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y) := by
-- proof
  apply StatMech.FK.ocd_inducedWiring_adj Gin Gout ιV bdryOut ψ x y

/--
[ocd_outsideGraph_le_fullGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outsideGraph_le_fullGraph_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop) :
-- imply
  ocd_outsideGraph Gout ιV bdryOut ψ ≤ ocd_fullGraph Gout ιV bdryOut ω ψ := by
-- proof
  apply StatMech.FK.ocd_outsideGraph_le_fullGraph Gin Gout ιV bdryOut ω ψ

/--
[ocd_psiExt_eq_false_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiExt_eq_false_of_range_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
  {e : Sym2 Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (he : e ∈ Set.range (ocd_innerEdge ιV)) :
-- imply
  ocd_psiExt ιV ψ ω e = ocd_psiExt ιV (fun _ => false) ω e := by
-- proof
  apply StatMech.FK.ocd_psiExt_eq_false_of_range Gin Gout ιV bdryOut hι ψ ω he

/--
[ocd_psiWiredGraph_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiWiredGraph_eq_sup_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV) :
-- imply
  ocd_fullGraph Gout ιV bdryOut ω ψ = ocd_innerImageGraph Gout ιV ω ⊔ ocd_outsideGraph Gout ιV bdryOut ψ := by
-- proof
  apply StatMech.FK.ocd_psiWiredGraph_eq_sup Gin Gout ιV bdryOut hι ψ ω

/--
[ocd_innerImageGraph_adj_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerImageGraph_adj_inner_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {u v : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (h : (ocd_innerImageGraph Gout ιV ω).Adj u v) :
-- imply
  ocd_IsInnerVert ιV u ∧ ocd_IsInnerVert ιV v := by
-- proof
  apply StatMech.FK.ocd_innerImageGraph_adj_inner Gin Gout ιV bdryOut hι ω h

/--
[ocd_innerImageGraph_adj_](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerImageGraph_adj__eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  (ocd_innerImageGraph Gout ιV ω).Adj (ιV x) (ιV y) ↔ (openSub Gin ω).Adj x y := by
-- proof
  apply StatMech.FK.ocd_innerImageGraph_adj_ Gin Gout ιV bdryOut hι hadjm ω x y

/--
[ocd_innerGraph_reachable_of_outsideReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerGraph_reachable_of_outsideReachable_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop)
  (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y)) :
-- imply
  (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.ocd_innerGraph_reachable_of_outsideReachable Gin Gout ιV bdryOut ω ψ h

/--
[ocd_fullGraph_reachable_of_innerGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullGraph_reachable_of_innerGraph_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (h : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y) :
-- imply
  (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y) := by
-- proof
  apply StatMech.FK.ocd_fullGraph_reachable_of_innerGraph Gin Gout ιV bdryOut hι hadjm ω ψ h

/--
[ocd_innerGraph_reachable_of_fullGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerGraph_reachable_of_fullGraph_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y)) :
-- imply
  (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.ocd_innerGraph_reachable_of_fullGraph Gin Gout ιV bdryOut hι hadjm ω ψ h

/--
[ocd_fullGraph_reachable_](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullGraph_reachable__eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {x y : Vin}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y) ↔ (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
-- proof
  apply StatMech.FK.ocd_fullGraph_reachable_ Gin Gout ιV bdryOut hι hadjm ω ψ x y

/--
[ocd_fullGraph_adj_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullGraph_adj_of_outside_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {u w : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hu : ¬ ocd_IsInnerVert ιV u)
  (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Adj u w) :
-- imply
  (ocd_outsideGraph Gout ιV bdryOut ψ).Adj u w := by
-- proof
  apply StatMech.FK.ocd_fullGraph_adj_of_outside Gin Gout ιV bdryOut hι ω ψ hu h

/--
[ocd_outsideOnly_self_not_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outsideOnly_self_not_inner_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
  {u : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u) :
-- imply
  ¬ ocd_IsInnerVert ιV u := by
-- proof
  apply StatMech.FK.ocd_outsideOnly_self_not_inner Gin Gout ιV bdryOut ψ hu

/--
[ocd_outsideOnly_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outsideOnly_of_reachable_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
  {u v : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
  (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u v) :
-- imply
  ocd_OutsideOnly Gout ιV bdryOut ψ v := by
-- proof
  apply StatMech.FK.ocd_outsideOnly_of_reachable Gin Gout ιV bdryOut ψ hu h

/--
[ocd_outsideGraph_reachable_of_fullGraph_outsideOnly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outsideGraph_reachable_of_fullGraph_outsideOnly_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {u w : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hu : ocd_OutsideOnly Gout ιV bdryOut ψ u)
  (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable u w) :
-- imply
  (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable u w := by
-- proof
  apply StatMech.FK.ocd_outsideGraph_reachable_of_fullGraph_outsideOnly Gin Gout ιV bdryOut hι ω ψ hu h

/--
[ocd_isOutsideOnly_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_isOutsideOnly_mk_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
  {v : Vout}
-- given
  (bdryOut : Vout → Prop) :
-- imply
  ocd_IsOutsideOnly Gout ιV bdryOut ψ ((ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v) ↔ ocd_OutsideOnly Gout ιV bdryOut ψ v := by
-- proof
  apply StatMech.FK.ocd_isOutsideOnly_mk Gin Gout ιV bdryOut ψ v

/--
[ocd_fullComponentMap_inl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullComponentMap_inl_mk_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {x : Vin}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ (Sum.inl ((ocd_innerGraph Gin Gout ιV bdryOut ω ψ).connectedComponentMk x)) = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk (ιV x) := by
-- proof
  apply StatMech.FK.ocd_fullComponentMap_inl_mk Gin Gout ιV bdryOut hι hadjm ω ψ x

/--
[ocd_fullComponentMap_inr_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullComponentMap_inr_mk_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
  {v : Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hv : ocd_IsOutsideOnly Gout ιV bdryOut ψ ((ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v)) :
-- imply
  ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ (Sum.inr ⟨(ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v, hv⟩) = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk v := by
-- proof
  apply StatMech.FK.ocd_fullComponentMap_inr_mk Gin Gout ιV bdryOut hι hadjm ω ψ v hv

/--
[ocd_fullComponentMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullComponentMap_injective_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  Function.Injective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
-- proof
  apply StatMech.FK.ocd_fullComponentMap_injective Gin Gout ιV bdryOut hι hadjm ω ψ

/--
[ocd_fullComponentMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_fullComponentMap_surjective_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  Function.Surjective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
-- proof
  apply StatMech.FK.ocd_fullComponentMap_surjective Gin Gout ιV bdryOut hι hadjm ω ψ

/--
[ocd_numClustersBC_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_numClustersBC_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ω : ConfigSpace (Sym2 Vin)}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) (ocd_psiExt ιV ψ ω) = numClustersBC Gin (ocd_inducedWiring Gout ιV bdryOut ψ) ω + ocd_outsideShift Gout ιV bdryOut ψ := by
-- proof
  apply StatMech.FK.ocd_numClustersBC_psiExt Gin Gout ιV bdryOut hι hadjm ω ψ

/--
[ocd_innerEdge_image_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerEdge_image_edgeFinset_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  Gin.edgeFinset.image (ocd_innerEdge ιV) = Gout.edgeFinset.filter (· ∈ Set.range (ocd_innerEdge ιV)) := by
-- proof
  apply StatMech.FK.ocd_innerEdge_image_edgeFinset Gin Gout ιV bdryOut hι hadjm

/--
[ocd_psiEdgeFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiEdgeFactor_pos_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
-- given
  (bdryOut : Vout → Prop)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  0 < ocd_psiEdgeFactor Gout ιV ψ p := by
-- proof
  apply StatMech.FK.ocd_psiEdgeFactor_pos Gin Gout ιV bdryOut hp hp1

/--
[ocd_edgeProduct_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_edgeProduct_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  edgeProduct Gout p (ocd_psiExt ιV ψ ω) = edgeProduct Gin p ω * ocd_psiEdgeFactor Gout ιV ψ p := by
-- proof
  apply StatMech.FK.ocd_edgeProduct_psiExt Gin Gout ιV bdryOut hι hadjm ψ ω

/--
[ocd_psiShift_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_psiShift_pos_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
-- given
  (bdryOut : Vout → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < ocd_psiShift Gout ιV bdryOut ψ p q := by
-- proof
  apply StatMech.FK.ocd_psiShift_pos Gin Gout ιV bdryOut hp hp1 hq

/--
[ocd_bcWeight_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_bcWeight_psiExt_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  bcWeight Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_psiExt ιV ψ ω) = bcWeight Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω * ocd_psiShift Gout ιV bdryOut ψ p q := by
-- proof
  apply StatMech.FK.ocd_bcWeight_psiExt Gin Gout ιV bdryOut hι hadjm ψ ω

/--
[ocd_inducedBcZ_psi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_inducedBcZ_psi_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV) :
-- imply
  inducedBcZ Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ = bcZ Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q * ocd_psiShift Gout ιV bdryOut ψ p q := by
-- proof
  apply StatMech.FK.ocd_inducedBcZ_psi Gin Gout ιV bdryOut hι hadjm ψ

/--
[ocd_condBcProb_psiExt_eq_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condBcProb_psiExt_eq_bcProb_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {ω : ConfigSpace (Sym2 Vin)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω) = bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
-- proof
  apply StatMech.FK.ocd_condBcProb_psiExt_eq_bcProb Gin Gout ιV bdryOut hι hadjm hp hp1 hq ψ ω

/--
[ocd_condBcProb_psiExt_sum_eq_inducedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condBcProb_psiExt_sum_eq_inducedBox_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) = ∑ ω : ConfigSpace (Sym2 Vin), (ocd_psiExt ιV ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
-- proof
  apply StatMech.FK.ocd_condBcProb_psiExt_sum_eq_inducedBox Gin Gout ιV bdryOut hι hadjm hp hp1 hq ψ B

/--
[ocd_condBcProb_psiExt_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condBcProb_psiExt_dominated_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  [DecidablePred bdryIn]
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (bdryIn : Vin → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
-- proof
  apply StatMech.FK.ocd_condBcProb_psiExt_dominated Gin Gout ιV bdryOut hι hadjm bdryIn hp hp1 hq ψ hwire hA

/--
[ocd_free_le_inducedBcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_free_le_inducedBcProb_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
-- proof
  apply StatMech.FK.ocd_free_le_inducedBcProb Gin Gout ιV bdryOut hι hadjm hp hp1 hq ψ hA

/--
[ocd_free_le_condBcProb_innerRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_free_le_condBcProb_innerRestrict_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤ ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1 : ℝ)) ρ * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ := by
-- proof
  apply StatMech.FK.ocd_free_le_condBcProb_innerRestrict Gin Gout ιV bdryOut hι hadjm hp hp1 hq ψ hA

/--
[ocd_condFibre_congr_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condFibre_congr_dom_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {ψ ψ' : ConfigSpace (Sym2 V)}
-- given
  (bdryOut : Vout → Prop)
  (h : AgreesOff F ψ ψ') :
-- imply
  condFibre F ψ = condFibre F ψ' := by
-- proof
  apply StatMech.FK.ocd_condFibre_congr_dom Gin Gout ιV bdryOut h

/--
[ocd_condBcProb_congr_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condBcProb_congr_dom_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ψ' ω : ConfigSpace (Sym2 V)}
-- given
  (bdryOut : Vout → Prop)
  (h : AgreesOff F ψ ψ') :
-- imply
  condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
-- proof
  apply StatMech.FK.ocd_condBcProb_congr_dom Gin Gout ιV bdryOut G C p q F ψ ψ' ω h

/--
[ocd_outProj_eq_false_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outProj_eq_false_of_range_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ρ : ConfigSpace (Sym2 Vout)}
  {e : Sym2 Vout}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (he : e ∈ Set.range (ocd_innerEdge ιV)) :
-- imply
  ocd_outProj ιV ρ e = false := by
-- proof
  apply StatMech.FK.ocd_outProj_eq_false_of_range Gin Gout ιV bdryOut hι ρ he

/--
[ocd_outProj_eq_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outProj_eq_of_not_range_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ρ : ConfigSpace (Sym2 Vout)}
  {e : Sym2 Vout}
-- given
  (bdryOut : Vout → Prop)
  (he : e ∉ Set.range (ocd_innerEdge ιV)) :
-- imply
  ocd_outProj ιV ρ e = ρ e := by
-- proof
  apply StatMech.FK.ocd_outProj_eq_of_not_range Gin Gout ιV bdryOut ρ he

/--
[ocd_outProj_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_outProj_idem_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ρ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV) :
-- imply
  ocd_outProj ιV (ocd_outProj ιV ρ) = ocd_outProj ιV ρ := by
-- proof
  apply StatMech.FK.ocd_outProj_idem Gin Gout ιV bdryOut hι ρ

/--
[ocd_filter_outProj_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_filter_outProj_eq_condFibre_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {ψ : ConfigSpace (Sym2 Vout)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hψ : ocd_outProj ιV ψ = ψ) :
-- imply
  Finset.univ.filter (fun ρ => ocd_outProj ιV ρ = ψ) = condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ := by
-- proof
  apply StatMech.FK.ocd_filter_outProj_eq_condFibre Gin Gout ιV bdryOut hι ψ hψ

/--
[ocd_sum_fibreMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_sum_fibreMass_eq_one_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ), (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ, bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) = 1 := by
-- proof
  apply StatMech.FK.ocd_sum_fibreMass_eq_one Gin Gout ιV bdryOut hι hp hp1 hq

/--
[ocd_bcProb_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_bcProb_decompose_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {p q : ℝ}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ) = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ), (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ, bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) := by
-- proof
  apply StatMech.FK.ocd_bcProb_decompose Gin Gout ιV bdryOut hι hp hp1 hq B

/--
[ocd_condBcProb_innerRestrict_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_condBcProb_innerRestrict_le_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  [DecidablePred bdryIn]
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (bdryIn : Vin → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
-- proof
  apply StatMech.FK.ocd_condBcProb_innerRestrict_le Gin Gout ιV bdryOut hι hadjm bdryIn hp hp1 hq ψ hwire hA

/--
[ocd_wired_inner_dominated_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_wired_inner_dominated_bcProb_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  [DecidablePred bdryIn]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (bdryIn : Vin → Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hwire : ∀ ψ : ConfigSpace (Sym2 Vout), ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
-- proof
  apply StatMech.FK.ocd_wired_inner_dominated_bcProb Gin Gout ιV bdryOut hι hadjm bdryIn hp hp1 hq hwire hA

/--
[ocd_latticeAdjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_latticeAdjMatch_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
-- given
  (bdryOut : Vout → Prop)
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) :
-- imply
  ocd_AdjMatch (SimpleGraph.comap Subtype.val (hypercubicLattice d)) (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV := by
-- proof
  apply StatMech.FK.ocd_latticeAdjMatch Gin Gout ιV bdryOut ιV hιval

/--
[ocd_bdryIn_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_bdryIn_of_outsideGraph_adj_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {x : {y : Site d // y ∈ Sin}}
  {z : {y : Site d // y ∈ Sout}}
-- given
  (bdryOut : Vout → Prop)
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
  (bdryOut : {y : Site d // y ∈ Sout} → Prop)
  (bdryIn : {y : Site d // y ∈ Sin} → Prop)
  (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
  (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d), NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
  (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout}))
  (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ).Adj (ιV x) z) :
-- imply
  bdryIn x := by
-- proof
  apply StatMech.FK.ocd_bdryIn_of_outsideGraph_adj Gin Gout ιV bdryOut ιV hιval bdryOut bdryIn hmargin hbdryIn ψ h

/--
[ocd_latticeInducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_latticeInducedWiring_le_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
-- given
  (bdryOut : Vout → Prop)
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
  (hιinj : Function.Injective ιV)
  (bdryOut : {y : Site d // y ∈ Sout} → Prop)
  (bdryIn : {y : Site d // y ∈ Sin} → Prop)
  (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
  (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d), NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
  (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout})) :
-- imply
  ocd_inducedWiring (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn := by
-- proof
  apply StatMech.FK.ocd_latticeInducedWiring_le Gin Gout ιV bdryOut ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn ψ

/--
[ocd_latticeWired_inner_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_latticeWired_inner_dominated_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 {y : Site d // y ∈ Sin}))}
-- given
  (bdryOut : Vout → Prop)
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
  (hιinj : Function.Injective ιV)
  (bdryOut : {y : Site d // y ∈ Sout} → Prop)
  (bdryIn : {y : Site d // y ∈ Sin} → Prop)
  (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
  (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d), NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q ρ) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q ω := by
-- proof
  apply StatMech.FK.ocd_latticeWired_inner_dominated Gin Gout ιV bdryOut ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn hp hp1 hq hA

/--
[ocd_innerRestrict_preimage_multiOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_innerRestrict_preimage_multiOpenEvent_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {t : Finset (Sym2 Vin)}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV) :
-- imply
  ocd_innerRestrict ιV ⁻¹' (med_genericMultiOpenEvent t) = med_genericMultiOpenEvent (t.image (ocd_innerEdge ιV)) := by
-- proof
  apply StatMech.FK.ocd_innerRestrict_preimage_multiOpenEvent Gin Gout ιV bdryOut hι t

/--
[ocd_latticeWired_multiMass_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean)
-/
@[path]
private lemma ocd_latticeWired_multiMass_dominated_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {Gin Gout ιV}
  (Gin Gout ιV)
  [DecidablePred bdryOut]
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  (Gin Gout ιV bdryOut)
  {Gin Gout ιV bdryOut}
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {p q : ℝ}
-- given
  (bdryOut : Vout → Prop)
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
  (hιinj : Function.Injective ιV)
  (bdryOut : {y : Site d // y ∈ Sout} → Prop)
  (bdryIn : {y : Site d // y ∈ Sin} → Prop)
  (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
  (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d), NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (t : Finset (Sym2 {y : Site d // y ∈ Sin})) :
-- imply
  med_multiMassProb (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q) (t.image (ocd_innerEdge ιV)) ≤ med_multiMassProb (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q) t := by
-- proof
  apply StatMech.FK.ocd_latticeWired_multiMass_dominated Gin Gout ιV bdryOut ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn hp hp1 hq t


-- created on 2026-10-23
