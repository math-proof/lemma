/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic
import Def.Combinatorics.Additive.ThreeSumset.Part2
open scoped Pointwise

/-!
# A three-sumset cardinality inequality

This file proves the Gyarmati-Matolcsi-Ruzsa inequality for three finite subsets of a prime field.

## Main statements

* `MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod`
-/


namespace MetaMathlibExt

theorem reps_nonempty {G : Type*} [DecidableEq G] [AddSemigroup G]
    {A B C : Finset G} {s : G} (hs : s ∈ A + B + C) : (reps A B C s).Nonempty := by
  rcases Finset.mem_add.1 hs with ⟨ab, hab, c, hc, habc⟩
  rcases Finset.mem_add.1 hab with ⟨a, ha, b, hb, hab⟩
  refine ⟨toLexTriple (a, (b, c)), mem_reps_iff.2 ⟨ha, hb, hc, ?_⟩⟩
  simp only [ofLexTriple_toLexTriple]
  rw [hab, habc]

end MetaMathlibExt
