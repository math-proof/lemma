import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedLemma5
open StatMech StatMech.Onsager


/--
[ons_weight_product_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_weight_product_surgery_eq
  {L n : ℕ}
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  (∏ k, weight (ons_portEdge L (ons_surgery e (ons_dartRev L) d k))) = ∏ k, weight (ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_weight_product_surgery weight e d hd

/--
[ons_loopWeight_KWmatWeighted_factor_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeighted_factor_one_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatWeighted L weight omega) d = (∏ k, weight (ons_portEdge L (d k))) * ons_loopWeight (ons_KWmat L 1 omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeighted_factor_one weight omega d

/--
[ons_KWmatWeighted_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_KWmatWeighted_surgery_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_KWmatWeighted L weight omega) (ons_surgery e (ons_dartRev L) d) = -ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeighted_surgery_sign weight omega homega e d hd

/--
[ons_KWmatWeightedPhase_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_surgery_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_surgery e (ons_dartRev L) d) = -ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_surgery_sign weight omega homega a b e d hd

/--
[ons_KWmatWeightedPhase_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_lemma5_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_lemma5 weight omega homega a b e

/--
[ons_weight_product_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_weight_product_loopRev_eq
  {L n : ℕ}
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {d : Fin n → ons_Dart L} :
-- imply
  (∏ k, weight (ons_portEdge L (ons_loopRev L d k))) = ∏ k, weight (ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_weight_product_loopRev weight d

/--
[ons_loopWeight_KWmatWeightedPhase_factor_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeightedPhase_factor_one_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d = (∏ k, weight (ons_portEdge L (d k))) * ons_loopWeight (ons_KWmatPhase L 1 omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeightedPhase_factor_one weight omega a b d

/--
[ons_loopWeight_KWmatWeightedPhase_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedLemma5.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeightedPhase_loopRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_loopRev L d) = ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeightedPhase_loopRev weight omega homega a b d


-- created on 2026-10-23
