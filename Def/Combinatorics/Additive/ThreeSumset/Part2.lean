/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic
import Theorem.Combinatorics.Additive.ThreeSumset
open scoped Pointwise

/-!
# A three-sumset cardinality inequality

This file proves the Gyarmati-Matolcsi-Ruzsa inequality for three finite subsets of a prime field.

## Main statements

* `MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod`
-/


namespace MetaMathlibExt

def reps {G : Type*} [DecidableEq G] [Add G]
    (A B C : Finset G) (s : G) : Finset (LexTriple G) :=
  ((A.product (B.product C)).filter fun x => x.1 + x.2.1 + x.2.2 = s).image toLexTriple

end MetaMathlibExt
