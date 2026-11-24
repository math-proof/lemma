module
public import Abbrev.Analysis.Section_3_2
public import Theorem.Nat.NotAxiomOfUniversalSpecification
public import Theorem.Set.Any_All_Disjoint.of.Ne_Empty


public section

namespace Chapter3

variable [SetTheory]

abbrev Russells_paradox : ¬ axiom_of_universal_specification :=
  _root_.Nat.NotAxiomOfUniversalSpecification

open SetTheory

open SetTheory.Set

abbrev SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A :=
  _root_.Set.Any_All_Disjoint.of.Ne_Empty (A := A) (h := h)

end Chapter3
