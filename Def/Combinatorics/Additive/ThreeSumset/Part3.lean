/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic
import Theorem.Combinatorics.Additive.ThreeSumset.Part2
open scoped Pointwise

/-!
# A three-sumset cardinality inequality

This file proves the Gyarmati-Matolcsi-Ruzsa inequality for three finite subsets of a prime field.

## Main statements

* `MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod`
-/


namespace MetaMathlibExt

noncomputable def canonicalRep {G : Type*} [DecidableEq G] [AddSemigroup G]
    [LinearOrder G] [Inhabited G] (A B C : Finset G) (s : G) : LexTriple G :=
  if hs : s ∈ A + B + C then (reps A B C s).min' (reps_nonempty hs)
  else toLexTriple (default, (default, default))

end MetaMathlibExt
