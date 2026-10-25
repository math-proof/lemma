import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Generic

variable (I : Ideal C)

theorem map_toIntAlgHom_le_of_smul_eq (g : G) (h : g • I = I) :
    I.map (MulSemiringAction.toRingHom G C g).toIntAlgHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap]
  have hmem : g • c ∈ g • I := Ideal.smul_mem_pointwise_smul g c I hc
  rw [h] at hmem
  exact hmem

end Generic
end AdicCompletion
