import Mathlib
import Lemma.GroupCohomology.Corestriction2

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

def IsSlotInvariant {G : Type*} [Group G] {X : Type*} {n : ℕ} (U : Subgroup G) (u : (Fin n → G) → X) : Prop :=
  ∀ g s : Fin n → G, (∀ i, s i ∈ U) → u (g * s) = u g

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G}

def resFin (A : Rep.{0} k G) (n : ℕ) (u : (Fin n → G) → A) : (Fin n → H) → A :=
  fun h => u (fun i => (h i : G))

-- corFin / corFin_apply extracted to Lemma.Fin.CorFin.eq.Sum (as CorFin)

end Cores
end groupCohomology
