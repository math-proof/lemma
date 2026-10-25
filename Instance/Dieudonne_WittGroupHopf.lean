-- Carved from Lemma/Definitions/Def_Dieudonne_WittGroupHopf.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Lemma.Dieudonne.WittGroupHopf

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation

namespace WittGroup

variable (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v)

noncomputable instance instCommRing : CommRing (Coord R p n J) :=
  inferInstanceAs (CommRing (MvPolynomial (J × Fin n) R))

noncomputable instance instAlgebra : Algebra R (Coord R p n J) :=
  inferInstanceAs (Algebra R (MvPolynomial (J × Fin n) R))

noncomputable instance instInhabited : Inhabited (Coord R p n J) := ⟨0⟩

variable {R p n J}

variable [hp : Fact p.Prime]


variable (R p n J)

variable {R p n J}


variable (R p n J)

noncomputable instance instBialgebra : Bialgebra R (Coord R p n J) :=
  Bialgebra.ofAlgHom (comul R p n J) (counit R p n J) (comul_coassoc R p n J)
    (comul_rTensor_counit R p n J) (comul_lTensor_counit R p n J)

noncomputable instance instHopfAlgebra : HopfAlgebra R (Coord R p n J) :=
  HopfAlgebra.ofAlgHom (antipode R p n J) (antipode_rTensor_comul R p n J) (antipode_lTensor_comul R p n J)

instance instIsCocomm : Coalgebra.IsCocomm R (Coord R p n J) := by
  refine ⟨?_⟩
  have h : (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.comp (comul R p n J) =
      comul R p n J := by
    refine algHom_ext fun j i => ?_
    let g : Coord R p n J ⊗[R] Coord R p n J →+* Coord R p n J ⊗[R] Coord R p n J :=
      (Algebra.TensorProduct.comm R (Coord R p n J) (Coord R p n J)).toAlgHom.toRingHom
    change g (comul R p n J (X j i)) = comul R p n J (X j i)
    rw [ringHom_comul_X, comul_X, add_comm]
    rfl
  refine LinearMap.ext fun x => ?_
  exact AlgHom.congr_fun h x

variable {R p n J}


end WittGroup

end Deformation
