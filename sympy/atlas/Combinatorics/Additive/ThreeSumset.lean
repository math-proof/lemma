/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean -/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic

/-!
# A three-sumset cardinality inequality

This file proves the Gyarmati-Matolcsi-Ruzsa inequality for three finite subsets of a prime field.

## Main statements

* `MetaMathlibExt.gyarmatiMatolcsiRuzsa_three_sumset_zmod`
-/

open scoped Pointwise

namespace MetaMathlibExt

private abbrev LexTriple (G : Type*) := G ×ₗ (G ×ₗ G)

private def toLexTriple {G : Type*} (x : G × (G × G)) : LexTriple G :=
  toLex (x.1, toLex x.2)

private def ofLexTriple {G : Type*} (x : LexTriple G) : G × (G × G) :=
  ((ofLex x).1, ((ofLex (ofLex x).2).1, (ofLex (ofLex x).2).2))

@[simp] private theorem ofLexTriple_toLexTriple {G : Type*} (x : G × (G × G)) :
    ofLexTriple (toLexTriple x) = x := rfl

@[simp] private theorem toLexTriple_ofLexTriple {G : Type*} (x : LexTriple G) :
    toLexTriple (ofLexTriple x) = x := by cases x; rfl

private def reps {G : Type*} [DecidableEq G] [Add G]
    (A B C : Finset G) (s : G) : Finset (LexTriple G) :=
  ((A.product (B.product C)).filter fun x => x.1 + x.2.1 + x.2.2 = s).image toLexTriple

private theorem reps_nonempty {G : Type*} [DecidableEq G] [AddSemigroup G]
    {A B C : Finset G} {s : G} (hs : s ∈ A + B + C) : (reps A B C s).Nonempty := by
  rcases Finset.mem_add.1 hs with ⟨ab, hab, c, hc, habc⟩
  rcases Finset.mem_add.1 hab with ⟨a, ha, b, hb, hab⟩
  refine ⟨toLexTriple (a, (b, c)), mem_reps_iff.2 ⟨ha, hb, hc, ?_⟩⟩
  simp only [ofLexTriple_toLexTriple]
  rw [hab, habc]

private noncomputable def canonicalRep {G : Type*} [DecidableEq G] [AddSemigroup G]
    [LinearOrder G] [Inhabited G] (A B C : Finset G) (s : G) : LexTriple G :=
  if hs : s ∈ A + B + C then (reps A B C s).min' (reps_nonempty hs)
  else toLexTriple (default, (default, default))
end MetaMathlibExt
