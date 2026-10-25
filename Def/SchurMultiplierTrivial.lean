import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open scoped commutatorElement

namespace Ihara

universe u

def HasTrivialSchurMultiplier (G : Type u) [Group G] : Prop :=
  ∀ (E : Type u) [Group E] (π : E →* G), Function.Surjective π →
    MonoidHom.ker π ≤ Subgroup.center E → MonoidHom.ker π ≤ commutator E →
      MonoidHom.ker π = ⊥

end Ihara
