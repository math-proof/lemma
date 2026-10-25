import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Def.AlgebraicGeometry_OModulePresheafEulerChar

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)


theorem cechFinrank_zero : F.cechFinrank K 0 = Module.finrank R (F.H0 K) := rfl

theorem cechFinrank_succ (i : ℕ) : F.cechFinrank K (i + 1) = Module.finrank R (F.HSucc K i) := rfl


theorem eulerChar_def :
    F.eulerChar K = ∑ i ∈ Finset.range (Fintype.card K.ι), (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := rfl

end AlgebraicGeometry.OModulePresheaf

end
