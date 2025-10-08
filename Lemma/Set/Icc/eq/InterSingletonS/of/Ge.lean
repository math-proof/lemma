import Lemma.Algebra.NotGt.is.Le
import Lemma.Set.Icc.eq.Empty.of.Gt
import Lemma.Set.InterSingletonS.subset.Icc
import Lemma.Set.EqEmpty.is.Subset_Empty
import Lemma.Nat.Eq.of.Le.Ge
open Algebra Set Nat


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  Icc x y = {x} ∩ {y} := by
-- proof
  
  by_cases h' : x > y
  · 
    have h := Icc.eq.Empty.of.Gt h'
    have h_subset := InterSingletonS.subset.Icc x y
    rw [h] at h_subset
    have h := EqEmpty.of.Subset_Empty h_subset
    aesop
  · 
    have h' := Le.of.NotGt h'
    have h := Eq.of.Le.Ge h' h
    aesop


-- created on 2025-08-04
