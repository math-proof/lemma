/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.ZMod.Basic
public import Theorem.Combinatorics.Additive.ThreeSumset.Part2

@[expose] public section

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
