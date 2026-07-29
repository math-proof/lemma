import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.AndBFn.is.AndBFnIte |
| comm | Bool.AndBFnIte.is.AndBFn |
| mp and | Bool.AndBFnIte.of.AndBFn |
| mpr and | Bool.AndBFn.of.AndBFnIte |
| mp.comm and | Bool.And_BFnIte.of.And_BFn |
| mpr.comm and | Bool.And_BFn.of.And_BFnIte |
| comm.is | Bool.And_BFn.is.And_BFnIte |
-/
@[main, comm, mp and, mpr and, mp.comm and, mpr.comm and, comm.is]
private lemma main
  [Decidable p]
-- given
  (R : α → β → Prop)
  (a b : α) :
-- imply
  R a c ∧ p ↔ R (if p then
    a
  else
    b) c ∧ p := by
-- proof
  aesop


-- created on 2025-07-29
