import Lemma.Int.EqNegNeg
open Int Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any.is.Any_UFnNeg |
| comm | Bool.Any_UFnNeg.is.Any |
| mp | Bool.Any_UFnNeg.of.Any |
| mpr | Bool.Any.of.Any_UFnNeg |
-/
@[main, comm, mp, mpr]
private lemma main
  [InvolutiveNeg α]
  {f : α → Prop} :
-- imply
  (∃ i, f i) ↔ (∃ i, f (-i)) := by
-- proof
  constructor
  <;>
    intro h
  <;>
    obtain ⟨i, hi⟩ := h
  <;>
    use -i
  .
    simpa [EqNegNeg] using hi


-- created on 2018-07-10
