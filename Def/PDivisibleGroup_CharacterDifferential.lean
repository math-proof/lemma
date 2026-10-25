import Mathlib
import Lemma.PDivisibleGroup.CartierDuality
import Lemma.PDivisibleGroup.Dimension

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra
open scoped TensorProduct

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section CotangentClass

variable (G : PDivisibleGroup R p h)

def cotangentClass (v : ℕ) : G.level v →ₗ[R] G.Cotangent v where
  toFun a := (G.augIdeal v).toCotangent
    ⟨a - algebraMap R (G.level v) (counit (R := R) a), Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩
  map_add' a b := by
    rw [← map_add]
    congr 1
    ext
    change a + b - algebraMap R (G.level v) (counit (R := R) (a + b)) =
      (a - algebraMap R (G.level v) (counit (R := R) a)) + (b - algebraMap R (G.level v) (counit (R := R) b))
    rw [map_add, map_add]
    abel
  map_smul' r a := by
    rw [RingHom.id_apply, ← LinearMap.map_smul_of_tower]
    congr 1
    ext
    change r • a - algebraMap R (G.level v) (counit (R := R) (r • a)) =
      r • (a - algebraMap R (G.level v) (counit (R := R) a))
    rw [map_smul, smul_sub, Algebra.smul_def r (algebraMap R (G.level v) _), ← map_mul, smul_eq_mul]

end CotangentClass

namespace CartierDuality

variable {G G' : PDivisibleGroup R p h} (D : CartierDuality G G')
variable (S : Type) [CommRing S] [Algebra R S]

def charElem (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.level v :=
  ∑ i, Point.toAlgHom ψ ((D.toDualEquiv v).symm ((Module.Free.chooseBasis R (G.level v)).coord i)) ⊗ₜ[R]
    Module.Free.chooseBasis R (G.level v) i


def charDiff (v : ℕ) (ψ : G'.Point S v) : S ⊗[R] G.Cotangent v :=
  (G.cotangentClass v).lTensor S (D.charElem S v ψ)

end CartierDuality

end PDivisibleGroup

end
