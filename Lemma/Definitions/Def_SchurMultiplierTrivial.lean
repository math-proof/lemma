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

theorem HasTrivialSchurMultiplier.of_mulEquiv {G H : Type u} [Group G] [Group H]
    (hH : HasTrivialSchurMultiplier H) (e : G ≃* H) : HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hker : MonoidHom.ker (e.toMonoidHom.comp π) = MonoidHom.ker π := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hsurj' : Function.Surjective (e.toMonoidHom.comp π) := by
    rw [MonoidHom.coe_comp]; exact e.surjective.comp hsurj
  have h := hH E (e.toMonoidHom.comp π) hsurj'
    (by rw [hker]; exact hcent) (by rw [hker]; exact hcomm)
  rw [← hker]; exact h

theorem hasTrivialSchurMultiplier_of_isCyclic {G : Type u} [Group G] [IsCyclic G] :
    HasTrivialSchurMultiplier G := by
  intro E _ π hsurj hcent hcomm
  have hcommutative : ∀ a b : E, a * b = b * a :=
    commutative_of_cyclic_center_quotient π hcent
  have hbot : commutator E = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcommutative g₁ g₂
  rw [eq_bot_iff]; exact hcomm.trans hbot.le

theorem hasTrivialSchurMultiplier_of_subsingleton {G : Type u} [Group G] [Subsingleton G] :
    HasTrivialSchurMultiplier G :=
  hasTrivialSchurMultiplier_of_isCyclic

end Ihara
