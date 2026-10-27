import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TheoryOfComputation.code.PolyTimeReducibility
open TuringMachine


/--
[inP_of_polyTimeReducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/PolyTimeReducibility.lean)
-/
@[path]
lemma inP_of_polyTimeReducible
  {Γ : Type}
  {A B : Set (List Γ)}
-- given
  (hAB : PolyTimeReducible A B)
  (hB : InP B) :
-- imply
  InP A :=
-- proof
  inP_of_polyReducible_inP hAB hB


-- created on 2026-10-23
