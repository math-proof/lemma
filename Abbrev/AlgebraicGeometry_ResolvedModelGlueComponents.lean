import Mathlib
import Lemma.AlgebraicGeometry.ResolvedModelGlueFibre

set_option maxHeartbeats 200000

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

abbrev Comps : Type := Fin 2 ⊕ (Σ n : N, Fin (C.thick n - 1))

section eta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))

  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)

  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end eta

end V3Glue.ChartInput

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open V3Glue.Aux

end AlgebraicGeometry

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section bridge

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

end bridge

section bridgeComp

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end bridgeComp

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, CategoryTheory.IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section exhaust

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

end exhaust

end V3Glue.ChartInput

namespace V3Glue.Aux.Layer0.W6a

variable {Y : Scheme.{u}}

end V3Glue.Aux.Layer0.W6a

section v3genPrimeAlgebra

open IsLocalRing

end v3genPrimeAlgebra

namespace AlgebraicGeometry

open V3Glue.Aux

open IsLocalRing TopologicalSpace

end AlgebraicGeometry

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry V3Glue.Aux.Layer0 TopologicalSpace IsLocalRing

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section transversalY

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

end transversalY

section transversal

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

end transversal

end V3Glue.ChartInput

namespace Topology.IsOpenEmbedding

end Topology.IsOpenEmbedding

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section maximal

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

end maximal

section maximalEta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

end maximalEta

end V3Glue.ChartInput

end
