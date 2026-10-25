import Mathlib
import Lemma.PDivisibleGroup.CartierDuality
import Lemma.PDivisibleGroup.Dimension
import Def.PDivisibleGroup_CharacterDifferential

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra
open scoped TensorProduct

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section CotangentClass

variable (G : PDivisibleGroup R p h)


theorem cotangentClass_apply (v : ℕ) (a : G.level v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent
      ⟨a - algebraMap R (G.level v) (counit (R := R) a),
        Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩ := rfl

theorem cotangentClass_of_mem (v : ℕ) (a : G.augIdeal v) :
    G.cotangentClass v a = (G.augIdeal v).toCotangent a := by
  rw [cotangentClass_apply]
  congr 1
  ext
  change (a : G.level v) - algebraMap R (G.level v) (counit (R := R) (a : G.level v)) = a
  rw [(G.mem_augIdeal_iff v a).mp a.2, map_zero, sub_zero]

@[simp] theorem cotangentClass_one (v : ℕ) : G.cotangentClass v 1 = 0 := by
  rw [cotangentClass_apply, ← map_zero (G.augIdeal v).toCotangent]
  congr 1
  ext
  change (1 : G.level v) - algebraMap R (G.level v) (counit (R := R) (1 : G.level v)) = 0
  rw [Bialgebra.counit_one, map_one, sub_self]

@[simp] theorem cotangentClass_algebraMap (v : ℕ) (r : R) :
    G.cotangentClass v (algebraMap R (G.level v) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cotangentClass_one, smul_zero]

end CotangentClass

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')
variable (S : Type) [CommRing S] [Algebra R S]


theorem charElem_def (v : ℕ) (ψ : G'.Point S v) :
    D.charElem S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R] Module.Free.chooseBasis R (G.level v) i :=
  rfl


theorem charDiff_def (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = (G.cotangentClass v).lTensor S (D.charElem S v ψ) := rfl

theorem charDiff_eq_sum (v : ℕ) (ψ : G'.Point S v) :
    D.charDiff S v ψ = ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm
      ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
        G.cotangentClass v (Module.Free.chooseBasis R (G.level v) i) := by
  rw [charDiff_def, charElem_def, map_sum]
  rfl

end CartierDuality

end PDivisibleGroup

end
