/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic
import Abbrev.Combinatorics.Additive.ThreeSumset
open scoped Pointwise

/-!
# A three-sumset cardinality inequality

This file proves the Gyarmati-Matolcsi-Ruzsa inequality for three finite subsets of a prime field.

## Main statements

* `MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod`
-/


namespace MetaMathlibExt

def toLexTriple {G : Type*} (x : G × (G × G)) : LexTriple G :=
  toLex (x.1, toLex x.2)

def ofLexTriple {G : Type*} (x : LexTriple G) : G × (G × G) :=
  ((ofLex x).1, ((ofLex (ofLex x).2).1, (ofLex (ofLex x).2).2))

end MetaMathlibExt
