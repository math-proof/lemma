import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Set.range Complex.ofReal) :
-- imply
  x = ~x := by
-- proof
  obtain ⟨r, rfl⟩ := h
  exact (Complex.conj_ofReal r).symm


-- created on 2023-05-02
