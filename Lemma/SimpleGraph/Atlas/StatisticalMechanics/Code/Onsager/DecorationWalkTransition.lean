import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationWalkTransition
open StatMech StatMech.Onsager


/--
[ons_isChain_closed_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_isChain_closed_ofFn_eq
  {R : alpha → alpha → Prop}
  {n : ℕ}
  [NeZero n]
  {f : Fin n → alpha}
-- given
  (hchain : List.IsChain R (List.ofFn f ++ [f 0])) :
-- imply
  ∀ k : Fin n, R (f k) (f (k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_isChain_closed_ofFn f hchain

/--
[ons_decDartIsExternal_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decDartIsExternal_symm_eq
  {L : ℕ}
  {a : (ons_decGraph L).Dart} :
-- imply
  ons_decDartIsExternal a.symm = ons_decDartIsExternal a := by
-- proof
  apply StatMech.Onsager.ons_decDartIsExternal_symm a

/--
[ons_decWalkExternalDarts_head_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_head_site_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {d : ons_Dart L}
-- given
  (hd : d ∈ (ons_decWalkExternalDarts p).head?) :
-- imply
  d.1 = u.1 := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_head_site p hd

/--
[ons_decWalkExternalDarts_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_isChain_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  List.IsChain (fun d e : ons_Dart L => ons_dirStep L d.2 d.1 = e.1) (ons_decWalkExternalDarts p) := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_isChain p

/--
[ons_decWalkExternalDarts_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_reverse_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v} :
-- imply
  ons_decWalkExternalDarts p.reverse = (ons_decWalkExternalDarts p).reverse.map (ons_dartRev L) := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_reverse p

/--
[ons_decWalkExternalDarts_getLast_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_getLast_site_eq
  {L : ℕ}
  {u v : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {d : ons_Dart L}
-- given
  (hd : d ∈ (ons_decWalkExternalDarts p).getLast?) :
-- imply
  ons_dirStep L d.2 d.1 = v.1 := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_getLast_site p hd

/--
[ons_decWalkExternalDarts_isChain_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decWalkExternalDarts_isChain_closed_eq
  {L : ℕ}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d} :
-- imply
  List.IsChain (fun e f : ons_Dart L => ons_dirStep L e.2 e.1 = f.1) (ons_decWalkExternalDarts q ++ [d]) := by
-- proof
  apply StatMech.Onsager.ons_decWalkExternalDarts_isChain_closed q

/--
[ons_decCycleFirstReturn_isChain_KW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_isChain_KW_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  List.IsChain (fun e f : ons_Dart L => e.1 = ons_dirStep L f.2 f.1) (ons_decCycleFirstReturn q) := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_isChain_KW q hq hsnd

/--
[ons_KWmatWeightedPhase_entry_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_entry_factor_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ}
  {d2 d1 : ons_Dart L} :
-- imply
  ons_KWmatWeightedPhase L weight omega u v d2 d1 = weight (ons_portEdge L d1) * ons_KWmatWeightedPhase L (fun _ => 1) omega u v d2 d1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_entry_factor L weight omega u v d2 d1

/--
[ons_edgeWeight_KWmatWeightedPhase_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_edgeWeight_KWmatWeightedPhase_factor_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ}
  {s : List (ons_Dart L)} :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L weight omega u v) s = ((s.tail.map (fun d => weight (ons_portEdge L d))).prod) * ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ => 1) omega u v) s := by
-- proof
  apply StatMech.Onsager.ons_edgeWeight_KWmatWeightedPhase_factor L weight omega u v s

/--
[ons_decCycleFirstReturn_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkTransition.lean)
-/
@[path]
private lemma ons_decCycleFirstReturn_weight_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega u v : ℂ}
-- given
  (hq : q.IsCycle)
  (hsnd : q.snd = ons_dartRev L d) :
-- imply
  ons_edgeWeight (ons_KWmatWeightedPhase L weight omega u v) (ons_decCycleFirstReturn q) = (∏ edge ∈ ons_walkOriginalEdges q, weight edge) * ons_edgeWeight (ons_KWmatWeightedPhase L (fun _ => 1) omega u v) (ons_decCycleFirstReturn q) := by
-- proof
  apply StatMech.Onsager.ons_decCycleFirstReturn_weight_factor q hq hsnd weight omega u v


-- created on 2026-10-23
