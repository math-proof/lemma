import Def.AlgebraicCurve_PlaceEvaluation
import Def.AlgebraicCurve_ComplexLineIntegral

set_option autoImplicit false

open scoped Manifold ContDiff Topology Real
open Set Complex

namespace AlgebraicCurve

structure RadialRegion where
  q : ℂ
  r : ℝ → ℝ
  hcont : Continuous r
  hper : Function.Periodic r (2 * π)
  hpos : ∀ φ, 0 < r φ
  N : ℕ
  φs : Fin (N + 1) → ℝ
  hφ0 : φs 0 = 0
  hφN : φs (Fin.last N) = 2 * π
  hmono : StrictMono φs
  hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))

namespace RadialRegion

def K (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ ≤ R.r (arg (z - R.q))}


noncomputable def loop (R : RadialRegion) (φ : ℝ) : ℂ := R.q + R.r φ * exp (φ * I)


def arcIcc (R : RadialRegion) (k : Fin R.N) : Set ℝ := Icc (R.φs k.castSucc) (R.φs k.succ)

def arcSet (R : RadialRegion) (k : Fin R.N) : Set ℂ := R.loop '' R.arcIcc k

end RadialRegion

structure AnalyticCoord (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where
  ζ : OpenPartialHomeomorph (Place ℂ F) ℂ
  analytic : ∀ P ∈ ζ.source,
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  deriv_ne : ∀ P ∈ ζ.source,
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0

namespace AnalyticCoord

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]


end AnalyticCoord

structure Cell (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] extends AnalyticCoord F where
  R : RadialRegion
  hKt : R.K ⊆ ζ.target

namespace Cell

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def carrier (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.K


noncomputable def bdry (C : Cell F) (φ : ℝ) : Place ℂ F := C.ζ.symm (C.R.loop φ)

def arc (C : Cell F) (k : Fin C.R.N) : Set (Place ℂ F) := C.ζ.symm '' C.R.arcSet k

end Cell

structure CellDissection (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where

  ιC : Type
  ιE : Type
  ιV : Type
  [fintypeC : Fintype ιC]
  [fintypeE : Fintype ιE]
  [fintypeV : Fintype ιV]
  [decEqC : DecidableEq ιC]
  [decEqE : DecidableEq ιE]
  [decEqV : DecidableEq ιV]
  cell : ιC → Cell F

  side : (C : ιC) → Fin (cell C).R.N → ιE × Bool

  side_bij : Function.Bijective fun p : (Σ C : ιC, Fin (cell C).R.N) => side p.1 p.2

  ends : ιE → ιV × ιV
  vert : ιV → Place ℂ F

  arc_ends : ∀ (C : ιC) (k : Fin (cell C).R.N),
    (cell C).bdry ((cell C).R.φs k.castSucc) =
        vert (if (side C k).2 then (ends (side C k).1).1 else (ends (side C k).1).2) ∧
      (cell C).bdry ((cell C).R.φs k.succ) =
        vert (if (side C k).2 then (ends (side C k).1).2 else (ends (side C k).1).1)

  arc_rev : ∀ (C : ιC) (k : Fin (cell C).R.N) (C' : ιC) (k' : Fin (cell C').R.N),
    (side C k).1 = (side C' k').1 → (side C k).2 = true → (side C' k').2 = false →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell C').R.arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
      ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
      ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
      ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)

  cover : ⋃ C, (cell C).carrier = univ

  inter : ∀ (C C' : ιC) (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
    Relation.ReflTransGen
      (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (side A k).1 = (side B k').1 ∧ x ∈ (cell A).arc k)
      C C'

  conn : ∀ C C' : ιC, Relation.ReflTransGen
    (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N), (side A k).1 = (side B k').1)
    C C'

attribute [instance] CellDissection.fintypeC CellDissection.fintypeE CellDissection.fintypeV
  CellDissection.decEqC CellDissection.decEqE CellDissection.decEqV

section Integrals

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]


end Integrals

end AlgebraicCurve
