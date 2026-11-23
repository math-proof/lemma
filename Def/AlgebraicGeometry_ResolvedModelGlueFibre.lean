import Mathlib
import Def.AlgebraicGeometry_ResolvedModelGlue

set_option maxHeartbeats 200000

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme

namespace V3Glue.Aux.Layer0.W6

variable {U C S : Scheme.{u}} (f : U ⟶ S) (ρ : C ⟶ S) (x : U)

noncomputable def fiberMap : (pullback.fst f ρ).fiber x ⟶ ρ.fiber (f x) :=
  pullback.map _ _ _ _ (pullback.snd f ρ) (Spec.map (f.residueFieldMap x)) f
    (IsPullback.of_hasPullback f ρ).w (by simp)

noncomputable def liftPt [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x)
    (o : C) (ho : ρ o = f x) : ↥(pullback f ρ) :=
  (existsUnique_snd_eq_of_apply_eq f ρ x hiii o ho).choose

noncomputable def fiberIso [IsIso (f.residueFieldMap x)] : (pullback.fst f ρ).fiber x ≅ ρ.fiber (f x) :=
  haveI := isIso_fiberMap f ρ x
  asIso (fiberMap f ρ x)

end V3Glue.Aux.Layer0.W6

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry V3Glue.Aux.Layer0 Scheme

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

def xU (n : N) : ↥(C.U n) := ⟨C.x n, C.x_mem_U n⟩

def vertex (n : N) : C.S n := (C.f n).base (C.xU n)

section fibre

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

include hRF in

def ε : (C.q n).fiber (C.xU n) ≅ (C.ρ n).fiber (C.vertex n) :=
  haveI := hRF
  W6.fiberIso (C.f n) (C.ρ n) (C.xU n)

end fibre

end V3Glue.ChartInput

end

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section lift

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

def liftY (o : C.Res n) (ho : C.ρ n o = C.vertex n) : C.Y n :=
  haveI := hRF
  W6.liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) o ho

def exPt (o : C.Res n) (ho : C.ρ n o = C.vertex n) : C.toGlueInput.glued :=
  C.toGlueInput.ιY n (C.liftY n hRF o ho)

end lift

section edge

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

def edgePt' (n : N) (d : Fin (C.thick n)) : C.toGlueInput.glued := C.exPt n (hRF n) (oRes n d) (hoRes n d)

end edge

end V3Glue.ChartInput


end
