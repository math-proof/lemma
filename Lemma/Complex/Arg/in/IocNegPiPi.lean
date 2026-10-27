import Notation.Analysis.Complex.Complexes
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (z : ℂ) :
-- imply
  arg z ∈ Ioc (-π) π :=
-- proof
  Complex.arg_mem_Ioc z


-- created on 2018-08-29
