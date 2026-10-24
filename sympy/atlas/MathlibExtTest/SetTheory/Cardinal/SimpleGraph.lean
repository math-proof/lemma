/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/SetTheory/Cardinal/SimpleGraph.lean -/


import sympy.atlas.SetTheory.Cardinal.SimpleGraph


open Ordinal Cardinal

-- Normal API use: the ordinal-cardinal Ramsey predicate accepts two
-- ordinals and a cardinal.
noncomputable example : Prop :=
  OrdinalCardinalRamsey (ω ^ ω : Ordinal.{0}) (ω ^ ω : Ordinal.{0}) (3 : Cardinal.{0})

-- Semantic check: the zero-color Ramsey statement holds via the empty
-- blue clique.
example : OrdinalCardinalRamsey (ω : Ordinal.{0}) (ω : Ordinal.{0}) (0 : Cardinal.{0}) := by
  intro red blue _
  right
  refine ⟨∅, fun x hx y hy _ => False.elim hx, ?_⟩
  simp
