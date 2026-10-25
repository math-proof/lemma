import Def.AlgebraicCurve_PlaceEvaluation
import Def.AlgebraicCurve_ComplexLineIntegral
import Structure.AlgebraicCurve_CellDissection

set_option autoImplicit false

open scoped Manifold ContDiff Topology Real
open Set Complex

namespace AlgebraicCurve


namespace RadialRegion


def Kint (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ < R.r (arg (z - R.q))}


noncomputable def loop' (R : RadialRegion) (φ : ℝ) : ℂ :=
  (((deriv R.r φ : ℝ) : ℂ) + R.r φ * I) * exp (φ * I)


end RadialRegion


namespace AnalyticCoord

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def read (A : AnalyticCoord F) (u : F) : ℂ → ℂ :=
  fun z => Place.evalAt (A.ζ.symm z) u

end AnalyticCoord


namespace Cell

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]


def interior' (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.Kint


end Cell


section Integrals

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def coeffIn (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (θ : Ω[F⁄ℂ]) (w : ℂ) : ℂ :=
  (ζ.symm w).readDifferential θ (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) (ζ.symm w)) *
    deriv (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) ∘ ζ.symm) w

noncomputable def Cell.bdryIntegrand (C : Cell F) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ :=
  coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s

noncomputable def CellDissection.arcOf (𝒟 : CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  Function.surjInv 𝒟.side_bij.surjective q

noncomputable def CellDissection.edgeInt (𝒟 : CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  ∫ s in ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)..
      ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
    (𝒟.cell (𝒟.arcOf (e, true)).1).bdryIntegrand θ s

def CellDissection.skeleton (𝒟 : CellDissection F) : Set (Place ℂ F) :=
  ⋃ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), (𝒟.cell p.1).arc p.2

end Integrals

end AlgebraicCurve
