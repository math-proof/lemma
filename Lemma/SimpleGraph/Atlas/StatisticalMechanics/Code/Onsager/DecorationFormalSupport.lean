import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationFormalSupport
open StatMech StatMech.Onsager


/--
[ons_sum_surgery_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_sum_surgery_invariant_eq
  [Fintype E]
  [DecidableEq E]
  [AddCommMonoid M]
  {n : ℕ}
  [NeZero n]
  {e : E}
  {rev : E → E}
  {f : E → M}
  {loop : Fin n → E}
-- given
  (hrev : Function.Involutive rev)
  (hf : ∀ x, f (rev x) = f x)
  (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
-- imply
  (∑ k, f (ons_surgery e rev loop k)) = ∑ k, f (loop k) := by
-- proof
  apply StatMech.Onsager.ons_sum_surgery_invariant e rev hrev f hf loop hloop

/--
[ons_decLoopExternalExponent_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExternalExponent_surgery_eq
  {L : ℕ}
  [NeZero L]
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (hloop : (∃ i, loop i = d) ∧ (∃ j, loop j = ons_dartRev L d)) :
-- imply
  ons_decLoopExternalExponent L (ons_surgery d (ons_dartRev L) loop) = ons_decLoopExternalExponent L loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopExternalExponent_surgery L d loop hloop

/--
[ons_decLoopInternalExponent_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopInternalExponent_surgery_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hloop : (∃ i, loop i = d) ∧ (∃ j, loop j = ons_dartRev L d)) :
-- imply
  ons_decLoopInternalExponent L (ons_surgery d (ons_dartRev L) loop) = ons_decLoopInternalExponent L loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopInternalExponent_surgery L d loop hvalid hloop

/--
[ons_decLoopExponent_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_surgery_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (loop k).1 = ons_dirStep L (loop (k + 1)).2 (loop (k + 1)).1)
  (hloop : (∃ i, loop i = d) ∧ (∃ j, loop j = ons_dartRev L d)) :
-- imply
  ons_decLoopExponent L (ons_surgery d (ons_dartRev L) loop) = ons_decLoopExponent L loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_surgery L d loop hvalid hloop

/--
[ons_decLoopScalar_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopScalar_surgery_sign_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
  {a b : Fin 2}
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hloop : (∃ i, loop i = d) ∧ (∃ j, loop j = ons_dartRev L d)) :
-- imply
  ons_decLoopScalar L omega (ons_spinPhase L a) (ons_spinPhase L b) (ons_surgery d (ons_dartRev L) loop) = -ons_decLoopScalar L omega (ons_spinPhase L a) (ons_spinPhase L b) loop := by
-- proof
  apply StatMech.Onsager.ons_decLoopScalar_surgery_sign L omega homega a b d loop hloop

/--
[ons_KWmatDecorationWeightedPhase_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_surgery_sign_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hloop : (∃ i, loop i = d) ∧ (∃ j, loop j = ons_dartRev L d)) :
-- imply
  ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_surgery d (ons_dartRev L) loop) = -ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_surgery_sign L decWeight omega homega a b d loop hloop

/--
[ons_KWmatDecorationWeightedPhase_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_lemma5_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) d (ons_dartRev L d), ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b)) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_lemma5 L decWeight omega homega a b d

/--
[ons_KWmatDecorationWeightedPhase_mask_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_mask_surgery_sign_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
  {loop : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
  (hloop : loop ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b))) (ons_surgery e (ons_dartRev L) loop) = -ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_mask_surgery_sign L decWeight omega homega a b forbidden hforbidden e loop hloop

/--
[ons_KWmatDecorationWeightedPhase_mask_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_mask_lemma5_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ∑ loop ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b))) loop = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_mask_lemma5 L decWeight omega homega a b forbidden hforbidden e

/--
[ons_loopWeight_KWmatDecorationWeightedPhase_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatDecorationWeightedPhase_loopRev_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {loop : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_loopRev L loop) = ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatDecorationWeightedPhase_loopRev L decWeight a b loop

/--
[ons_loopWeight_KWmatDecorationWeightedPhase_mask_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatDecorationWeightedPhase_mask_loopRev_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {loop : Fin n → ons_Dart L}
-- given
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) (ons_loopRev L loop) = ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b))) loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatDecorationWeightedPhase_mask_loopRev L decWeight a b forbidden hforbidden loop

/--
[ons_externalDecoratedEdge_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_externalDecoratedEdge_eq_iff_eq
  {L : ℕ}
  {d e : ons_Dart L} :
-- imply
  s(e, ons_dartRev L e) = s(d, ons_dartRev L d) ↔ e = d ∨ e = ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_externalDecoratedEdge_eq_iff L d e

/--
[ons_decChainEdge_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decChainEdge_eq_iff_eq
  {L : ℕ}
  {site site' : ZMod L × ZMod L}
  {i j : Fin 3} :
-- imply
  ons_decChainEdge site i = ons_decChainEdge site' j ↔ site = site' ∧ i = j := by
-- proof
  apply StatMech.Onsager.ons_decChainEdge_eq_iff site site' i j

/--
[ons_decLoopInternalExponent_chain_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopInternalExponent_chain_apply_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decLoopInternalExponent L loop (ons_decChainEdge site i) = ∑ k, if (loop k).1 = site ∧ i ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopInternalExponent_chain_apply L loop site i

/--
[ons_decLoopExternalExponent_chain_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExternalExponent_chain_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decLoopExternalExponent L loop (ons_decChainEdge site i) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExternalExponent_chain_apply L loop site i

/--
[ons_decLoopExponent_chain_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_chain_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decLoopExponent L loop (ons_decChainEdge site i) = ∑ k, if (loop k).1 = site ∧ i ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2 then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_chain_apply L loop site i

/--
[ons_decLoopExponent_chain_apply_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_chain_apply_eq_card_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_decLoopExponent L loop (ons_decChainEdge site i) = (Finset.univ.filter fun k => (loop k).1 = site ∧ i ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2).card := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_chain_apply_eq_card L loop site i

/--
[ons_two_le_decLoopExponent_chain_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_two_le_decLoopExponent_chain_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  2 ≤ ons_decLoopExponent L loop (ons_decChainEdge site i) ↔ ∃ k j : Fin n, k ≠ j ∧ (loop k).1 = site ∧ i ∈ ons_decChainPathIndices ((loop (k + 1)).2 + 2) (loop k).2 ∧ (loop j).1 = site ∧ i ∈ ons_decChainPathIndices ((loop (j + 1)).2 + 2) (loop j).2 := by
-- proof
  apply StatMech.Onsager.ons_two_le_decLoopExponent_chain_iff L loop site i

/--
[ons_decLoopInternalExponent_external_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopInternalExponent_external_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {d : ons_Dart L} :
-- imply
  ons_decLoopInternalExponent L loop s(d, ons_dartRev L d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopInternalExponent_external_apply L loop d

/--
[ons_decLoopExternalExponent_external_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExternalExponent_external_apply_eq
  {L : ℕ}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {d : ons_Dart L} :
-- imply
  ons_decLoopExternalExponent L loop s(d, ons_dartRev L d) = ∑ k, if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExternalExponent_external_apply L loop d

/--
[ons_decLoopExponent_external_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_external_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {d : ons_Dart L} :
-- imply
  ons_decLoopExponent L loop s(d, ons_dartRev L d) = ∑ k, if loop k = d ∨ loop k = ons_dartRev L d then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_external_apply L loop d

/--
[ons_decLoopExponent_external_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_external_pos_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → ons_Dart L}
  {d : ons_Dart L} :
-- imply
  0 < ons_decLoopExponent L loop s(d, ons_dartRev L d) ↔ (∃ k, loop k = d) ∨ ∃ k, loop k = ons_dartRev L d := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_external_pos_iff L loop d

/--
[ons_decLoopExponent_apply_eq_zero_of_not_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decLoopExponent_apply_eq_zero_of_not_mem_edgeFinset_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {edge : ons_DecEdge L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hedge : edge ∉ (ons_decGraph L).edgeFinset) :
-- imply
  ons_decLoopExponent L d edge = 0 := by
-- proof
  apply StatMech.Onsager.ons_decLoopExponent_apply_eq_zero_of_not_mem_edgeFinset L d hvalid edge hedge

/--
[ons_decFormalLogCoeff_eq_zero_of_offGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decFormalLogCoeff_eq_zero_of_offGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ}
  {edge : ons_DecEdge L}
-- given
  (hedge : edge ∉ (ons_decGraph L).edgeFinset)
  (hmedge : m edge ≠ 0) :
-- imply
  ons_decFormalLogCoeff L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) m = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalLogCoeff_eq_zero_of_offGraph L a b m edge hedge hmedge

/--
[ons_decFormalRoot_coeff_eq_zero_of_offGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSupport.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_eq_zero_of_offGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ}
  {edge : ons_DecEdge L}
-- given
  (hedge : edge ∉ (ons_decGraph L).edgeFinset)
  (hmedge : m edge ≠ 0) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_eq_zero_of_offGraph L a b m edge hedge hmedge


-- created on 2026-10-23
