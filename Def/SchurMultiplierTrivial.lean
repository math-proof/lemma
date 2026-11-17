module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

open scoped commutatorElement

namespace Ihara

universe u

def HasTrivialSchurMultiplier (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] (π : E →* G), Function.Surjective π →
    MonoidHom.ker π ≤ Subgroup.center E → MonoidHom.ker π ≤ commutator E →
      MonoidHom.ker π = ⊥

end Ihara
