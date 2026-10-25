-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FGSubalgebraTensorStage.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_FGSubalgebra
import Abbrev.AlgebraicGeometry_FGSubalgebraTensorStage

set_option autoImplicit false

universe u

open TensorProduct

namespace AlgebraicGeometry.FGSubalgebra

variable (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Algebra k A]


instance tensorStage_directedSystem : DirectedSystem (tensorStage k A Γ) (fun i j h => tensorStageMap k A Γ i j h) where
  map_self := fun i x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, hx, hy]
  map_map := fun i j l hij hjl x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul γ d => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.FGSubalgebra
