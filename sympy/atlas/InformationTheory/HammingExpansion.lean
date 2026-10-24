/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/HammingExpansion.lean -/

import sympy.atlas.InformationTheory.HammingBall
import Lemma.Real.HammingBall
namespace Hamming

/-!
# Generic Hamming expansion and ball predicates

ATLAS item N134 (ProbabilisticMethodsInCombinatorics:134). Reusable generic
support extracted while reformalizing that item. Source:
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean`
(lines 17--39) at commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean#L17-L39>

Source-to-API map: ATLAS's duplicate Hamming distance and ball map to
existing `hammingDist` and `Hamming.ball`, while ATLAS's expansion operator and ball
predicate map to `Hamming.expansion` and `Hamming.IsBall`.

This module is a supporting step, not the full N134 target; the Wanted module
states the full ball-comparison target. The Harper theorem itself is not
proved here.
-/

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- The `t`-expansion of `A`: all points at Hamming distance at most `t` from some
element of `A`, as the union of `ball a t` over `a ∈ A`. -/
def expansion (A : Finset (ι → F)) (t : ℕ) : Finset (ι → F) :=
  A.biUnion fun a => ball a t

/-- A subset `B` of the Hamming space is a Hamming ball if `B = ball c e`
for some center `c` and radius `e`. -/
def IsBall (B : Finset (ι → F)) : Prop :=
  ∃ c : ι → F, ∃ e : ℕ, B = ball c e
end Hamming
