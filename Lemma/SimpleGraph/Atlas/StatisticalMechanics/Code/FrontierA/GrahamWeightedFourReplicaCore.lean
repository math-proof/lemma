import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamOfEdgeFun_add4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean)
-/
@[path]
private lemma grahamOfEdgeFun_add4_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (a b c d : G.edgeFinset -> Nat) :
-- imply
  (fun e => ofEdgeFun G a e + ofEdgeFun G b e + ofEdgeFun G c e + ofEdgeFun G d e) = ofEdgeFun G (fun e => a e + b e + c e + d e) := by
-- proof
  apply StatMech.FrontierA.grahamOfEdgeFun_add4 G a b c d

/--
[grahamWeight_mul4_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean)
-/
@[path]
private lemma grahamWeight_mul4_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {a b c d : Current V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  weight G beta J a * weight G beta J b * weight G beta J c * weight G beta J d = (∏ e ∈ G.edgeFinset, (Nat.choose (a e + b e + c e + d e) (a e) : Real) * (Nat.choose (b e + c e + d e) (b e) : Real) * (Nat.choose (c e + d e) (c e) : Real)) * weight G beta J (fun e => a e + b e + c e + d e) := by
-- proof
  apply StatMech.FrontierA.grahamWeight_mul4_eq G beta J a b c d

/--
[grahamWeight_split4_eq_binom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean)
-/
@[path]
private lemma grahamWeight_split4_eq_binom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (total a b c : G.edgeFinset -> Nat)
  (habc : ∀ e, a e + b e + c e ≤ total e) :
-- imply
  weight G beta J (ofEdgeFun G a) * weight G beta J (ofEdgeFun G b) * weight G beta J (ofEdgeFun G c) * weight G beta J (ofEdgeFun G (fun e => total e - a e - b e - c e)) = (∏ e : G.edgeFinset, (Nat.choose (total e) (a e) : Real) * (Nat.choose (total e - a e) (b e) : Real) * (Nat.choose (total e - a e - b e) (c e) : Real)) * weight G beta J (ofEdgeFun G total) := by
-- proof
  apply StatMech.FrontierA.grahamWeight_split4_eq_binom G beta J total a b c habc


-- created on 2026-10-23
