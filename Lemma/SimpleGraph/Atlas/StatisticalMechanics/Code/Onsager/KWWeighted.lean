import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWWeighted
open StatMech StatMech.Onsager


/--
[ons_KWmatWeighted_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean)
-/
@[path]
private lemma ons_KWmatWeighted_const_eq
  {L : ℕ}
  {x omega : ℂ} :
-- imply
  ons_KWmatWeighted L (fun _ => x) omega = ons_KWmat L x omega := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeighted_const L x omega

/--
[ons_loopWeight_KWmatWeighted_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeighted_eq_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  ons_loopWeight (ons_KWmatWeighted L weight omega) d = (∏ k, weight (ons_portEdge L (d k))) * ∏ k, ons_turnW omega (d (k + 1)).2 (d k).2 := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeighted_eq weight omega d hvalid

/--
[ons_KWmatWeightedPhase_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_const_eq
  {L : ℕ}
  {x omega u v : ℂ} :
-- imply
  ons_KWmatWeightedPhase L (fun _ => x) omega u v = ons_KWmatPhase L x omega u v := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_const L x omega u v

/--
[ons_loopWeight_KWmatWeightedPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeightedPhase_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatWeightedPhase L weight omega u v) d = (∏ k, ons_dirPhase u v (d k).2) * ons_loopWeight (ons_KWmatWeighted L weight omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeightedPhase weight omega u v d


-- created on 2026-10-23
