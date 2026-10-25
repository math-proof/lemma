import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.GaloisAction.Part3
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Stabilizer

variable (𝔫 : Ideal C)

@[simp]
theorem stabilizer_smul_of (d : MulAction.stabilizer G 𝔫) (c : C) :
    d • of 𝔫 C c = of 𝔫 C ((d : G) • c) :=
  smul_of' 𝔫 (fun d => d.2) d c

theorem evalₐ_stabilizer_smul (d : MulAction.stabilizer G 𝔫) (n : ℕ) (c : C)
    (x : AdicCompletion 𝔫 C) (hx : evalₐ 𝔫 n x = Ideal.Quotient.mk (𝔫 ^ n) c) :
    evalₐ 𝔫 n (d • x) = Ideal.Quotient.mk (𝔫 ^ n) ((d : G) • c) :=
  evalₐ_smul' 𝔫 (fun d => d.2) d n c x hx

end Stabilizer

section MapIdeal

variable {O : Type w} [CommRing O] [Algebra O C]

theorem smul_algebraMap_eq [SMulCommClass G O C] (g : G) (o : O) :
    g • algebraMap O C o = algebraMap O C o := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_map_algebraMap_eq [SMulCommClass G O C] (J : Ideal O) (g : G) :
    g • J.map (algebraMap O C) = J.map (algebraMap O C) := by
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  congr 1
  ext o
  exact smul_algebraMap_eq g o

end MapIdeal
end AdicCompletion
