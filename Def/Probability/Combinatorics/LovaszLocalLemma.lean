/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

@[expose] public section

set_option linter.unusedSectionVars false

open Finset SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
# Finite symmetric Lovász Local Lemma

This file proves the finite symmetric Lovász Local Lemma: given a finite
probability space with a finite family of bad events whose dependency graph
has maximum degree at most `d`, if each bad event has probability at most `p`
and `Real.exp 1 * p * (d + 1) ≤ 1`, then with strictly positive probability
none of the bad events occur.

Reference for the exact `Real.exp 1 * p * (d + 1) ≤ 1` criterion: N. Alon and
J. H. Spencer, The Probabilistic Method, third edition, John Wiley & Sons, 2008,
Corollary 5.1.2 (“The Local Lemma; Symmetric Case”). The original local lemma is due to
P. Erdős and L. Lovász, “Problems and results on 3-chromatic hypergraphs and some related
questions,” Infinite and Finite Sets, Colloq. Math. Soc. János Bolyai 10 (1975), 609–627,
whose Lemma 2 gives the earlier weaker `4 * p * d ≤ 1` symmetric estimate.

## Main result

- `MathlibExt.Probability.Combinatorics.LovaszLocalLemma.lovasz_local_lemma_symmetric_finite`:
  the finite symmetric Lovász Local Lemma.
-/


namespace MathlibExt.Probability.Combinatorics.LovaszLocalLemma

variable {Ω : Type*} {I : Type*}

/-- Probability of a set: sum of pmf over members. -/
noncomputable def prob [Fintype Ω] (pmf : Ω → ℝ) (E : Set Ω) : ℝ :=
  ∑ ω : Ω, (if ω ∈ E then pmf ω else 0)

/-- Good set: no bad events in S occur. -/
def goodSet (A : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ j ∈ S, ω ∉ A j}

/-- All set: all bad events in S occur. -/
def allSet (A : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ j ∈ S, ω ∈ A j}

end MathlibExt.Probability.Combinatorics.LovaszLocalLemma
