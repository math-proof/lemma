import sympy.analysis.Section_3_2
import Lemma.Nat.NotAxiomOfUniversalSpecification
import Lemma.Set.Any_All_Disjoint.of.Ne_Empty

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
