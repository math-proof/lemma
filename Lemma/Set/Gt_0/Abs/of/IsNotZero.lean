import sympy.functions.elementary.complexes
import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Set.range Complex.ofReal \ {0}) :
-- imply
  ‖x‖ > 0 :=
-- proof
  norm_pos_iff.mpr (fun hx => h.2 hx)


-- created on 2020-04-11
