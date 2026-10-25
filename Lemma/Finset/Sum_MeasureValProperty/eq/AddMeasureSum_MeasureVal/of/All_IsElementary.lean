import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary
open Classical


/--
[IsElementary.sum_insert_split](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {a: Set (EuclideanSpace' d)}
  {S': Finset (Set (EuclideanSpace' d))}
-- given
  (ha : a ∉ S')
  (hE: ∀ E ∈ insert a S', IsElementary E) :
-- imply
  ∑ E:(insert a S' : Finset (Set (EuclideanSpace' d))), (hE E.val E.property).measure =
    (hE a (Finset.mem_insert_self _ _)).measure +
    ∑ E:S', (hE E.val (Finset.mem_insert_of_mem E.property)).measure :=
-- proof
  IsElementary.sum_insert_split ha hE


-- created on 2026-10-22
