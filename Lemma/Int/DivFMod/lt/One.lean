import Lemma.Int.LtFMod.of.Gt_0
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Int.GtCoeS.is.Gt
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Int.GtFMod.of.Lt_0
import Lemma.Nat.NotGt.is.Le
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Rat.LtDivS.of.Gt.Lt_0
import Lemma.Rat.Div.eq.One.of.Lt_0
open Nat Int Rat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (n.fmod d) / (d : ℚ) < 1 := by
-- proof
  by_cases h : d > 0
  have := LtFMod.of.Gt_0 (n := n) h
  have := LtCoeS.of.Lt (R := ℚ) this
  have h' := GtCoeS.of.Gt (R := ℚ) h
  have := LtDivS.of.Lt.Gt_0 this h'
  rwa [Div.eq.One.of.Gt_0 h'] at this
  by_cases h' : d = 0
  rw [h']
  norm_num
  have h := Le.of.NotGt h
  have h := Lt.of.Le.Ne h' h
  have := GtFMod.of.Lt_0 (n := n) h
  have := GtCoeS.of.Gt (R := ℚ) this
  have h' := LtCoeS.of.Lt (R := ℚ) h
  have := LtDivS.of.Gt.Lt_0 this h'
  rwa [Div.eq.One.of.Lt_0 h'] at this


-- created on 2025-03-28
-- updated on 2025-03-30
