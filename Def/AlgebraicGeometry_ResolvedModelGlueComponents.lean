import Mathlib
import Lemma.Scheme.ResolvedModelGlueFibre
import Abbrev.AlgebraicGeometry_ResolvedModelGlueComponents

set_option maxHeartbeats 200000

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section eta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))

  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)

  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

def ξY (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) : C.Y n := C.j n ⟨ξ j, hU, hξ j⟩

def ηG : C.Comps → C.toGlueInput.glued
  | Sum.inl j => C.toGlueInput.ιX0 ⟨ξ j, hξ j⟩
  | Sum.inr ⟨n, k⟩ => C.exPt n (hRF n) (gRes n k) (hgRes n k)

def compG (v : C.Comps) : C.toGlueInput.glued.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {C.ηG hRF gRes hgRes ξ hξ v}, isClosed_closure⟩

variable (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

end eta

end V3Glue.ChartInput


namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)


section bridgeComp

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end bridgeComp

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry TopologicalSpace Scheme

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, CategoryTheory.IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

def chainPos' (n : N) (d : ℕ) : C.Comps :=
  if h0 : d = 0 then Sum.inl 0
  else if h : d < C.thick n then Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩
  else Sum.inl 1

def dEnd (n : N) (j : Fin 2) : Fin (C.thick n) :=
  ⟨if j = 0 then 0 else C.thick n - 1, by have := C.one_le_thick n; split_ifs <;> omega⟩

section exhaust

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

end exhaust

end V3Glue.ChartInput


namespace AlgebraicGeometry

open V3Glue.Aux

open IsLocalRing TopologicalSpace

def Scheme.v3genPrime (X : Scheme.{u}) {a b : X} (h : a ⤳ b) : Ideal (X.presheaf.stalk b) :=
  (maximalIdeal (X.presheaf.stalk a)).comap (X.presheaf.stalkSpecializes h).hom

end AlgebraicGeometry

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry V3Glue.Aux.Layer0 TopologicalSpace IsLocalRing Scheme

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)


section transversal

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

end transversal

end V3Glue.ChartInput


namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Scheme

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)


section maximalEta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end maximalEta

end V3Glue.ChartInput

end
