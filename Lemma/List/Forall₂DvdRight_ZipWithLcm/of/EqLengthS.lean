import sympy.core.mul
import sympy.Basic
import Lemma.List.ZipWithLcm.comm.of.EqLengthS
import Lemma.List.Forall₂DvdLeft_ZipWithLcm.of.EqLengthS
open List


@[main]
private lemma main
-- given
  (s s' : List ℕ)
  (h : s.length = s'.length) :
-- imply
  List.Forall₂ (fun a b => a ∣ b) s' (s.zipWith Nat.lcm s') := by
-- proof
  rw [ZipWithLcm.comm.of.EqLengthS s s' h]
  exact Forall₂DvdLeft_ZipWithLcm.of.EqLengthS s' s h.symm


-- created on 2026-10-07
