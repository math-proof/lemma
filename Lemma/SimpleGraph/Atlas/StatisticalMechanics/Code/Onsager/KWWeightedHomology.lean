import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedHomology
open StatMech StatMech.Onsager


/--
[ons_spinPhase_product_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedHomology.lean)
-/
@[path]
private lemma ons_spinPhase_product_eq_homology_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2) = ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_product_eq_homology a b d hvalid hsite hnu

/--
[ons_loopWeight_weightedPhase_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedHomology.lean)
-/
@[path]
private lemma ons_loopWeight_weightedPhase_eq_homology_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d = ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) * ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_weightedPhase_eq_homology weight omega a b d hvalid hsite hnu

/--
[ons_loopWeight_weightedPhase_eq_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedHomology.lean)
-/
@[path]
private lemma ons_loopWeight_weightedPhase_eq_spinCharacter_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
  (hgeom : ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 = -(ons_spinCharacter 0 0 (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d = -(ons_spinCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * ∏ k, weight (ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_weightedPhase_eq_spinCharacter weight omega a b d hvalid hsite hnu hgeom


-- created on 2026-10-23
