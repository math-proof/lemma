import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
open StatMech StatMech.Onsager


/--
[ons_liftSite_outgoingDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_liftSite_outgoingDart_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n} :
-- imply
  (ons_liftSite v k, ons_liftDir v k) = v (-k) := by
-- proof
  apply StatMech.Onsager.ons_liftSite_outgoingDart v k

/--
[ons_liftSite_incomingRevDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_liftSite_incomingRevDart_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  (ons_liftSite v k, ons_liftDir v (k - 1) + 2) = ons_dartRev L (v (-k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_liftSite_incomingRevDart v hvalid k

/--
[ons_portEdge_mem_dartEdgeSet_at_liftSite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_portEdge_mem_dartEdgeSet_at_liftSite_iff_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {k : Fin n}
  {mu : Fin 4}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1)) :
-- imply
  ons_portEdge L (ons_liftSite v k, mu) ∈ ons_dartEdgeSet v ↔ mu = ons_liftDir v k ∨ mu = ons_liftDir v (k - 1) + 2 := by
-- proof
  apply StatMech.Onsager.ons_portEdge_mem_dartEdgeSet_at_liftSite_iff v hvalid hsite k mu

/--
[ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hhom : ons_evenHomology L F = 0) :
-- imply
  ons_zeroFluxPotential F p + ons_zeroFluxPotential F (p.1, p.2 - 1) = ons_horizontalZBit F p := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology L F hF hhom p

/--
[ons_zeroFluxPotential_vertical_boundary_of_zeroHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_zeroFluxPotential_vertical_boundary_of_zeroHomology_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hhom : ons_evenHomology L F = 0) :
-- imply
  ons_zeroFluxPotential F p + ons_zeroFluxPotential F (p.1 - 1, p.2) = ons_verticalZBit F p := by
-- proof
  apply StatMech.Onsager.ons_zeroFluxPotential_vertical_boundary_of_zeroHomology L F hF hhom p

/--
[ons_sum_signedHorizontalBoundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_signedHorizontalBoundary_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {P : (ZMod L × ZMod L) → ZMod 2} :
-- imply
  ∑ p, ons_signedHorizontalBoundary P p = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_signedHorizontalBoundary_eq_zero P

/--
[ons_sum_signedVerticalBoundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_signedVerticalBoundary_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {P : (ZMod L × ZMod L) → ZMod 2} :
-- imply
  ∑ p, ons_signedVerticalBoundary P p = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_signedVerticalBoundary_eq_zero P

/--
[ons_outgoingBoundaryCoeff_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_outgoingBoundaryCoeff_divergence_eq
  {L : ℕ}
  {P : (ZMod L × ZMod L) → ZMod 2}
  {p : ZMod L × ZMod L} :
-- imply
  ∑ mu : Fin 4, ons_outgoingBoundaryCoeff P p mu = 0 := by
-- proof
  apply StatMech.Onsager.ons_outgoingBoundaryCoeff_divergence P p

/--
[ons_intVal_sub_eq_zero_of_fin2_add_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_intVal_sub_eq_zero_of_fin2_add_eq_zero_eq
  {a b : ZMod 2}
-- given
  (h : a + b = 0) :
-- imply
  (a.val : ℤ) - b.val = 0 := by
-- proof
  apply StatMech.Onsager.ons_intVal_sub_eq_zero_of_fin2_add_eq_zero a b h

/--
[ons_outgoingBoundaryCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_outgoingBoundaryCoeff_eq_zero_of_not_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
  {mu : Fin 4}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hhom : ons_evenHomology L F = 0)
  (hnot : ons_portEdge L (p, mu) ∉ F) :
-- imply
  ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) p mu = 0 := by
-- proof
  apply StatMech.Onsager.ons_outgoingBoundaryCoeff_eq_zero_of_not_mem L F hF hhom p mu hnot

/--
[ons_outgoingBoundaryCoeff_dartRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_outgoingBoundaryCoeff_dartRev_eq
  {L : ℕ}
  {P : (ZMod L × ZMod L) → ZMod 2}
  {d : ons_Dart L} :
-- imply
  ons_outgoingBoundaryCoeff P (ons_dartRev L d).1 (ons_dartRev L d).2 = -ons_outgoingBoundaryCoeff P d.1 d.2 := by
-- proof
  apply StatMech.Onsager.ons_outgoingBoundaryCoeff_dartRev P d

/--
[ons_fin4_sum_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_fin4_sum_eq_two_eq
  {f : Fin 4 → ℤ}
  {a b : Fin 4}
-- given
  (hab : a ≠ b)
  (hzero : ∀ mu, mu ≠ a → mu ≠ b → f mu = 0) :
-- imply
  ∑ mu, f mu = f a + f b := by
-- proof
  apply StatMech.Onsager.ons_fin4_sum_eq_two f a b hab hzero

/--
[ons_loopBoundaryCoeff_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_loopBoundaryCoeff_pred_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {k : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hFedge : F = ons_dartEdgeSet v)
  (hhom : ons_evenHomology L F = 0) :
-- imply
  ons_loopBoundaryCoeff (ons_zeroFluxPotential F) v k = ons_loopBoundaryCoeff (ons_zeroFluxPotential F) v (k - 1) := by
-- proof
  apply StatMech.Onsager.ons_loopBoundaryCoeff_pred v hvalid hsite hnu F hF hFedge hhom k

/--
[ons_fin_pred_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_fin_pred_invariant_eq
  {n : ℕ}
  [NeZero n]
  {f : Fin n → ℤ}
-- given
  (hpred : ∀ k, f k = f (k - 1)) :
-- imply
  ∀ k, f k = f 0 := by
-- proof
  apply StatMech.Onsager.ons_fin_pred_invariant f hpred

/--
[ons_intVal_sub_ne_zero_of_fin2_add_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_intVal_sub_ne_zero_of_fin2_add_eq_one_eq
  {a b : ZMod 2}
-- given
  (h : a + b = 1) :
-- imply
  (a.val : ℤ) - b.val ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_intVal_sub_ne_zero_of_fin2_add_eq_one a b h

/--
[ons_outgoingBoundaryCoeff_ne_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_outgoingBoundaryCoeff_ne_zero_of_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
  {mu : Fin 4}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hhom : ons_evenHomology L F = 0)
  (hmem : ons_portEdge L (p, mu) ∈ F) :
-- imply
  ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) p mu ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_outgoingBoundaryCoeff_ne_zero_of_mem L F hF hhom p mu hmem

/--
[ons_xWrapSign_eq_zero_of_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_xWrapSign_eq_zero_of_not_eq
  {L : ℕ}
  {d : ons_Dart L}
-- given
  (h : ¬ons_xWrap d) :
-- imply
  ons_xWrapSign d = 0 := by
-- proof
  apply StatMech.Onsager.ons_xWrapSign_eq_zero_of_not d h

/--
[ons_yWrapSign_eq_zero_of_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_yWrapSign_eq_zero_of_not_eq
  {L : ℕ}
  {d : ons_Dart L}
-- given
  (h : ¬ons_yWrap d) :
-- imply
  ons_yWrapSign d = 0 := by
-- proof
  apply StatMech.Onsager.ons_yWrapSign_eq_zero_of_not d h

/--
[ons_portEdge_eq_xSeamPortEdge_of_xWrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_portEdge_eq_xSeamPortEdge_of_xWrap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
-- given
  (h : ons_xWrap d) :
-- imply
  ons_portEdge L d = ons_xSeamPortEdge L d.1.2 := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_xSeamPortEdge_of_xWrap d h

/--
[ons_portEdge_eq_ySeamPortEdge_of_yWrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_portEdge_eq_ySeamPortEdge_of_yWrap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
-- given
  (h : ons_yWrap d) :
-- imply
  ons_portEdge L d = ons_ySeamPortEdge L d.1.1 := by
-- proof
  apply StatMech.Onsager.ons_portEdge_eq_ySeamPortEdge_of_yWrap d h

/--
[ons_boundaryCoeff_mul_xWrapSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_boundaryCoeff_mul_xWrapSign_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : (ZMod L × ZMod L) → ZMod 2}
  {d : ons_Dart L}
-- given
  (h : ons_xWrap d) :
-- imply
  ons_outgoingBoundaryCoeff P d.1 d.2 * ons_xWrapSign d = ons_signedHorizontalBoundary P (-1, d.1.2) := by
-- proof
  apply StatMech.Onsager.ons_boundaryCoeff_mul_xWrapSign P d h

/--
[ons_boundaryCoeff_mul_yWrapSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_boundaryCoeff_mul_yWrapSign_eq
  {L : ℕ}
  [Fact (2 < L)]
  {P : (ZMod L × ZMod L) → ZMod 2}
  {d : ons_Dart L}
-- given
  (h : ons_yWrap d) :
-- imply
  ons_outgoingBoundaryCoeff P d.1 d.2 * ons_yWrapSign d = ons_signedVerticalBoundary P (d.1.1, -1) := by
-- proof
  apply StatMech.Onsager.ons_boundaryCoeff_mul_yWrapSign P d h

/--
[ons_sum_signedHorizontalBoundary_fixed_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_signedHorizontalBoundary_fixed_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {P : (ZMod L × ZMod L) → ZMod 2}
  {x : ZMod L} :
-- imply
  ∑ y, ons_signedHorizontalBoundary P (x, y) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_signedHorizontalBoundary_fixed_eq_zero P x

/--
[ons_sum_signedVerticalBoundary_fixed_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_signedVerticalBoundary_fixed_eq_zero_eq
  {L : ℕ}
  [NeZero L]
  {P : (ZMod L × ZMod L) → ZMod 2}
  {y : ZMod L} :
-- imply
  ∑ x, ons_signedVerticalBoundary P (x, y) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_signedVerticalBoundary_fixed_eq_zero P y

/--
[ons_sum_boundaryCoeff_mul_xWrapSign_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_boundaryCoeff_mul_xWrapSign_eq_zero_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hFedge : F = ons_dartEdgeSet v)
  (hhom : ons_evenHomology L F = 0) :
-- imply
  ∑ j, ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) (v j).1 (v j).2 * ons_xWrapSign (v j) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_boundaryCoeff_mul_xWrapSign_eq_zero v hvalid hsite hnu F hF hFedge hhom

/--
[ons_sum_boundaryCoeff_mul_yWrapSign_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_sum_boundaryCoeff_mul_yWrapSign_eq_zero_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hFedge : F = ons_dartEdgeSet v)
  (hhom : ons_evenHomology L F = 0) :
-- imply
  ∑ j, ons_outgoingBoundaryCoeff (ons_zeroFluxPotential F) (v j).1 (v j).2 * ons_yWrapSign (v j) = 0 := by
-- proof
  apply StatMech.Onsager.ons_sum_boundaryCoeff_mul_yWrapSign_eq_zero v hvalid hsite hnu F hF hFedge hhom

/--
[ons_simpleLoop_zeroHomology_winding_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean)
-/
@[path]
private lemma ons_simpleLoop_zeroHomology_winding_eq_zero_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hF : ons_dartEdgeSet v ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
  (hhom : ons_evenHomology L (ons_dartEdgeSet v) = 0) :
-- imply
  (∑ k, ons_dirExponentX (v k).2) = 0 ∧ (∑ k, ons_dirExponentY (v k).2) = 0 := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_zeroHomology_winding_eq_zero v hvalid hsite hnu hF hhom


-- created on 2026-10-23
