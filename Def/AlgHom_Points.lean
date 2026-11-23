import Mathlib
import Def.AlgHom_Basic
import Def.WeierstrassCurve_TateModule
import Instance.PDivisibleGroup_Points

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace PDivisibleGroup.Hopf

section AntipodeAlgHom

open HopfAlgebra

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]

def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R) antipode_one fun a b => by
    rw [antipode_mul, mul_comm]

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H K : Type*} [CommSemiring H] [CommSemiring K]
  [Bialgebra R H] [Bialgebra R K]
variable (A : Type*) [CommSemiring A] [Algebra R A]

def convCompMonoidHom (π : H →ₐc[R] K) : WithConv (K →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] K))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

end ConvComp

end PDivisibleGroup.Hopf

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (L : Type) [CommRing L] [Algebra R L]

def Point (v : ℕ) : Type := WithConv (G.level v →ₐ[R] L)

namespace Point

variable {G L} {v : ℕ}

def toConv (x : G.Point L v) : WithConv (G.level v →ₐ[R] L) := x

def ofConv (f : WithConv (G.level v →ₐ[R] L)) : G.Point L v := f

def toAlgHom (x : G.Point L v) : G.level v →ₐ[R] L := WithConv.ofConv x

def ofAlgHom (f : G.level v →ₐ[R] L) : G.Point L v := WithConv.toConv f

end Point

noncomputable def pointIncl (v : ℕ) : G.Point L v →* G.Point L (v + 1) :=
  Hopf.convCompMonoidHom L (G.transition v)

variable {L}

variable (L)

noncomputable def pointInclLE {v w : ℕ} (hvw : v ≤ w) : G.Point L v →* G.Point L w :=
  Nat.leRec (motive := fun w _ => G.Point L v →* G.Point L w) (MonoidHom.id _)
    (fun w _ ih => (G.pointIncl L w).comp ih) hvw

variable {L}

noncomputable abbrev pointsDirectedSystemMap (v w : ℕ) (hvw : v ≤ w) :
    Additive (G.Point L v) →+ Additive (G.Point L w) :=
  MonoidHom.toAdditive (G.pointInclLE L hvw)

variable (L)

def Points : Type :=
  AddCommGroup.DirectLimit (fun v => Additive (G.Point L v)) fun v w hvw => G.pointsDirectedSystemMap v w hvw

noncomputable def pointsMkAdd (v : ℕ) : Additive (G.Point L v) →+ G.Points L :=
  AddCommGroup.DirectLimit.of (fun v => Additive (G.Point L v))
    (fun v w hvw => G.pointsDirectedSystemMap v w hvw) v

noncomputable def pointsMk (v : ℕ) : G.Point L v →* Multiplicative (G.Points L) :=
  AddMonoidHom.toMultiplicativeRight (G.pointsMkAdd L v)

variable {L}

section Map

variable {L' : Type} [CommRing L'] [Algebra R L'] {L'' : Type} [CommRing L''] [Algebra R L'']

def pointMap (φ : L →ₐ[R] L') (v : ℕ) : G.Point L v →* G.Point L' v where
  toFun x := Point.ofAlgHom (φ.comp (Point.toAlgHom x))
  map_one' := by
    apply congrArg Point.ofAlgHom
    change φ.comp ((Algebra.ofId R L).comp (counitAlgHom R (G.level v))) =
      (Algebra.ofId R L').comp (counitAlgHom R (G.level v))
    rw [← AlgHom.comp_assoc, Algebra.comp_ofId]
  map_mul' x y := by
    apply congrArg Point.ofConv
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib φ (Point.toConv x) (Point.toConv y)

noncomputable def pointsMap (φ : L →ₐ[R] L') : G.Points L →+ G.Points L' :=
  AddCommGroup.DirectLimit.map (G := fun v => Additive (G.Point L v)) (G' := fun v => Additive (G.Point L' v))
    (f := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (f' := fun v w hvw => G.pointsDirectedSystemMap v w hvw)
    (fun v => MonoidHom.toAdditive (G.pointMap φ v))
    (fun _ _ hvw => AddMonoidHom.ext fun x =>
      congrArg Additive.ofMul (G.pointMap_pointInclLE φ hvw (Additive.toMul x)))

end Map

section Tate

variable [Fact p.Prime]
variable (L)

abbrev tateModule : AddSubgroup (ℕ → G.Points L) := TateModule p (G.Points L)

noncomputable abbrev tateModuleRep : (L ≃ₐ[R] L) →* Module.End ℤ_[p] (TateModule p (G.Points L)) :=
  TateModule.rep p (G.Points L) (L ≃ₐ[R] L)

end Tate

end PDivisibleGroup

end
