/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HormanderFundamental
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- Shorthand for the standard `n`-dimensional Euclidean space `ℝⁿ` used throughout
the cone-support and wavefront-set development. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Shorthand for the unit sphere `S^{n-1} ⊆ ℝⁿ`, viewed as `Metric.sphere 0 1`. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E n) 1

/-- `IsConicCutoffNear g ω` says that `g : ℝⁿ → ℂ` is a smooth conic cutoff function
adapted to a unit-sphere direction `ω`. Concretely: `g` is `C^∞`, vanishes near the
origin, and agrees outside some small ball with a degree-`0` positively homogeneous
function `ψ` that does not vanish at `ω`. -/
def IsConicCutoffNear (g : E n → ℂ) (ω : Sphere n) : Prop :=
  ContDiff ℝ ↑(⊤ : ℕ∞) g ∧
  ∃ (R : ℝ), 0 < R ∧ R < 1 ∧
    ∃ (R₀ : ℝ), 0 < R₀ ∧ Function.support g ⊆ {x : E n | R₀ ≤ ‖x‖} ∧
    ∃ (ψ : E n → ℂ),
      (∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x) ∧
      ψ (ω : E n) ≠ 0 ∧
      (∀ x : E n, R < ‖x‖ → g x = ψ x)

/-- The *cone support on the sphere* of a tempered distribution `u`: the directions
`ω` at infinity for which no conic cutoff `g` near `ω` kills `u`, i.e., for which
`g · u ≠ 0` for every conic cutoff. -/
def ConeSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- `IsSmoothNear u x` says that `u` is *smooth near `x`*: there exists a smooth
compactly supported `φ` with `φ x ≠ 0` such that `φ · u` is (the embedding of) a
Schwartz function. This is the local Schwartz-representation criterion. -/
def IsSmoothNear (u : 𝓢'(E n, ℂ)) (x : E n) : Prop :=
  ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ x ≠ 0 ∧
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ u = (f : 𝓢'(E n, ℂ))

/-- The *singular support* of `u` (classical, in the interior): the set of points
`x` at which `u` fails to be smooth, in the sense of `IsSmoothNear`. -/
def singularSupport (u : 𝓢'(E n, ℂ)) : Set (E n) :=
  {x | ¬ IsSmoothNear u x}

/-- The *conic singular support on the sphere*: directions `ω` for which no conic
cutoff `g` near `ω` makes `g · u` (the embedding of) a Schwartz function. This is
the asymptotic singular support of `u` at infinity. -/
def ConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         ∃ (f : SchwartzMap (E n) ℂ),
           TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ))}

/-- The *cone support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`: the
distributional support in the interior, together with the cone support on the
sphere at infinity. -/
def coneSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (Distribution.dsupport u) ∪ Sum.inr '' (ConeSupportSphere u)

/-- The *cone singular support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`:
the singular support in the interior, plus the conic singular support on the
sphere at infinity. -/
def coneSingularSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (singularSupport u) ∪ Sum.inr '' (ConicSingularSupportSphere u)

/-- The (classical) *wavefront set* of `u`: the set of pairs `(x, ω)` such
that no smooth compactly supported bump `φ` nonzero at `x` produces a
distribution `φ · u` whose Fourier transform is conically smooth at `ω`. -/
def wavefrontSet (u : 𝓢'(E n, ℂ)) : Set (E n × Sphere n) :=
  {p | ¬ ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ p.1 ≠ 0 ∧
    p.2 ∉ ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))}

/-- The *scattering wavefront set at infinity*: the contribution to the
wavefront set parametrised by sphere directions at infinity, with the second
factor in the cone singular support of `𝓕 (g · u)`. -/
def scatteringWavefrontSetAtInfinity (u : 𝓢'(E n, ℂ)) : Set (Sphere n × (E n ⊕ Sphere n)) :=
  {q | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g q.1 ∧
    q.2 ∉ coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))}

/-- The *scattering wavefront set* of a tempered distribution `u`, obtained
by combining the classical wavefront set with the wavefront set at infinity. -/
def scatteringWavefrontSet (u : 𝓢'(E n, ℂ)) : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  (Prod.map Sum.inl Sum.inr '' wavefrontSet u) ∪
  (Prod.map Sum.inr id '' scatteringWavefrontSetAtInfinity u)

/-- The *conic support on the sphere* (duplicated definition kept for
backward-compatibility with earlier statements). -/
def ConicSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- A tempered distribution `u` is *compactly supported* if it vanishes on any
Schwartz function whose support is disjoint from some compact set `K`. -/
def IsCompactlySupportedDistribution (u : 𝓢'(E n, ℂ)) : Prop :=
  ∃ K : Set (E n), IsCompact K ∧
    ∀ f : 𝓢(E n, ℂ), (Function.support (⇑f) ∩ K = ∅) → u f = 0

/-- The *direction* of a nonzero vector `x ∈ ℝⁿ`, namely `x / ‖x‖` viewed as
a point of the unit sphere. -/
def directionOf {n : ℕ} (x : E n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x, by
    simp [Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos (inv_pos.mpr
      (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩


/-- If `Γ ⊆ 𝕊ⁿ⁻¹` is closed and disjoint from the conic singular support of
`u`, then `u` admits a decomposition `u = u₁' + u₁'' + u₂` where `u₁'` is
compactly supported, `u₁''` vanishes on Schwartz functions whose nonzero
points all have direction in `Γ`, `u₂` is Schwartz, and the conic support of
`u₁' + u₁''` is disjoint from `Γ`. -/
abbrev schwEmbed : 𝓢(E n, ℂ) →L[ℂ] 𝓢'(E n, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM (E n) ℂ

/-- A decomposition of a tempered distribution `u` into a Schwartz part and a
compactly supported part. -/
structure SchwartzCompactDecomp (u : 𝓢'(E n, ℂ)) where
  schwartzPart : 𝓢(E n, ℂ)
  compactPart : 𝓢'(E n, ℂ)
  compactPart_isCompactlySupported : IsCompactlySupportedDistribution compactPart
  sum_eq : u = schwEmbed schwartzPart + compactPart

/-- Predicate stating that `u` admits at least one `SchwartzCompactDecomp`,
and any two such decompositions differ by a compactly supported distribution. -/
structure HasEmptyConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Prop where
  hasDecomp : Nonempty (SchwartzCompactDecomp u)
  diff_compactlySupported : ∀ (d₁ d₂ : SchwartzCompactDecomp u),
    IsCompactlySupportedDistribution (schwEmbed d₁.schwartzPart - schwEmbed d₂.schwartzPart)

/-- Abstract data for performing convolutions of tempered distributions: a
"Schwartz-against" operator that is additive, a "compact-against" operator
that is additive, and a compatibility condition saying the two agree when the
input is compactly supported. -/
structure ConvolutionSystem (n : ℕ) where
  convSchwartz : 𝓢(E n, ℂ) → 𝓢'(E n, ℂ)
  convCompact : 𝓢'(E n, ℂ) → 𝓢'(E n, ℂ)
  convSchwartz_add : ∀ φ₁ φ₂, convSchwartz (φ₁ + φ₂) = convSchwartz φ₁ + convSchwartz φ₂
  convCompact_add : ∀ u₁ u₂, convCompact (u₁ + u₂) = convCompact u₁ + convCompact u₂
  convSchwartz_eq_compact : ∀ φ : 𝓢(E n, ℂ),
    IsCompactlySupportedDistribution (schwEmbed φ) →
    convSchwartz φ = convCompact (schwEmbed φ)


/-- If `ConicSingularSupportSphere u = ∅`, then `u` has the structure of an
empty conic singular support — it admits a Schwartz/compact decomposition
with the diff-compactness property. -/
def schwartzReflectionCLM : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- The convolution `u * φ` of a tempered distribution `u` with a Schwartz
function `φ`, defined as the tempered distribution `ψ ↦ u(φ̌ * ψ)` where
`φ̌(x) = φ(-x)`. -/
def schwartzConvolution
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ)) :
    TemperedDistribution (E n) ℂ :=
  u.comp ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) (schwartzReflectionCLM φ))


/-- Convolution of a tempered distribution `v` with a Schwartz function `φ`,
viewed as a tempered distribution. -/
def schwDistribConv (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ) :=
  schwartzConvolution v φ

/-- Specialisation of `convolution_decomp_well_defined` to the standard
convolution system when the conic singular support of `u` is empty. -/
def sphereNeg (ω : Sphere n) : Sphere n :=
  ⟨-ω.1, mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp ω.2)⟩

/-- The image of a set `S ⊆ 𝕊ⁿ⁻¹` under the antipodal map. -/
def negSet (S : Set (Sphere n)) : Set (Sphere n) :=
  sphereNeg '' S

/-- The reflection of a tempered distribution `v`: the distribution
`φ ↦ v(φ ∘ -id)`. -/
def reflection (v : TemperedDistribution (E n) ℂ) :
    TemperedDistribution (E n) ℂ :=
  v.comp schwartzReflectionCLM


/-- If the conic-cutoff `g₀ · u` is already Schwartz, then `g₀ · (u * φ)` is also Schwartz
for any Schwartz `φ`. -/
def DisjointCssCondition (u v : TemperedDistribution (E n) ℂ) : Prop :=
  ∀ ω : Sphere n, ω ∈ ConicSingularSupportSphere u →
    sphereNeg ω ∉ ConicSingularSupportSphere v

/-- "Open neighbourhood" formulation of the wavefront set complement: if `(x₀, ω₀)` is not
in `WF(u)`, there are open neighbourhoods `U ∋ x₀` and `V ∋ ω₀` such that for every cutoff
`φ'` supported in `U`, `V` is disjoint from `Css (𝓕 (φ' · u))`. -/
theorem exists_conicCutoff (ω : Sphere n) :
    ∃ (g : E n → ℂ), IsConicCutoffNear g ω := by

  let χ : ContDiffBump (0 : E n) := ⟨1/3, 2/3, by positivity, by norm_num⟩
  refine ⟨fun x => Complex.ofReal (1 - χ x), ?_, 2/3, by positivity, by norm_num,
    1/3, by positivity, ?_, fun _ => 1, ?_, ?_, ?_⟩
  ·
    rw [contDiff_infty]
    intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp (contDiff_const.sub χ.contDiff)

  ·
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_setOf_eq]
    by_contra h
    simp only [not_le] at h
    have hx_ball : x ∈ Metric.closedBall (0 : E n) χ.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt h
    have : χ x = 1 := χ.one_of_mem_closedBall hx_ball
    simp only [this, sub_self, Complex.ofReal_zero] at hx
    exact hx rfl
  ·
    intro a _ x _; rfl
  ·
    exact one_ne_zero
  ·
    intro x hx
    have hx_out : χ.rOut ≤ dist x 0 := by
      simp only [dist_zero_right]; exact le_of_lt hx
    have : χ x = 0 := χ.zero_of_le_dist hx_out
    simp only [this, sub_zero, Complex.ofReal_one]

/-- The closed unit ball in `ℝⁿ`, used as a compactification of Euclidean space for
defining the scattering wavefront set. -/
def ClosedBall : Type := {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

/-- The subspace topology on the closed unit ball. -/
instance : TopologicalSpace (ClosedBall n) :=
  inferInstanceAs (TopologicalSpace {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1})

/-- The set of pairs `(p, q)` in `ClosedBall × ClosedBall` for which at least one factor
lies on the boundary sphere. -/
def BoundaryProd : Set (ClosedBall n × ClosedBall n) :=
  {pq | ‖pq.1.val‖ = 1 ∨ ‖pq.2.val‖ = 1}

/-- Antipodal map on the closed ball. -/
def ClosedBall.neg (p : ClosedBall n) : ClosedBall n :=
  ⟨-p.val, by rw [norm_neg]; exact p.property⟩

/-- The closed ball has a `Neg` instance given by the antipodal map. -/
instance : Neg (ClosedBall n) where
  neg := ClosedBall.neg n

/-- Computing the underlying vector of `-p`: it is `-p.val`. -/
@[simp]
theorem ClosedBall.neg_val (p : ClosedBall n) : (-p).val = -p.val := rfl

/-- The antipodal map is an involution: `-(-p) = p`. -/
@[simp]
theorem ClosedBall.neg_neg (p : ClosedBall n) : -(-p) = p := by
  apply Subtype.ext
  simp [ClosedBall.neg_val]

variable {n}

/-- Boundary points of the closed ball are spherical directions. -/
def ClosedBall.toSphere (p : ClosedBall n) (hp : ‖p.val‖ = 1) : ConeSupport.Sphere n :=
  ⟨p.val, by simp [Metric.mem_sphere, dist_zero_right, hp]⟩

/-- Interior points of the closed ball map back to Euclidean space via the
"de-compactification" formula `p ↦ (1 - ‖p‖)⁻¹ p`. -/
def ClosedBall.toEuclidean (p : ClosedBall n) (hp : ‖p.val‖ < 1) :
    EuclideanSpace ℝ (Fin n) :=
  (1 - ‖p.val‖)⁻¹ • p.val

/-- The conic singular support `Css u` on the closed ball: at boundary points it agrees
with the spherical conic singular support, at interior points (after de-compactification)
it agrees with the usual singular support. -/
def Css (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConicSingularSupportSphere u
       else

        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ ConeSupport.singularSupport u}

/-- The cone support `Csp u` on the closed ball: at boundary points it agrees with the
spherical cone support, at interior points (after de-compactification) it agrees with the
distributional support of `u`. -/
def Csp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConeSupportSphere u
       else
        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ Distribution.dsupport u}

/-- Bundled statement: `Csp u`, `Css u`, and their sphere analogues are all closed; and a
"disjoint Css ⇒ Schwartz" statement holds. -/
def WFsc (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (ClosedBall n × ClosedBall n) :=
  {pq | ¬ (
    if h : ‖pq.1.val‖ = 1 then

      ∃ (g : ConeSupport.E n → ℂ),
        ConeSupport.IsConicCutoffNear g (pq.1.toSphere h) ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))
    else

      have hp : ‖pq.1.val‖ < 1 := lt_of_le_of_ne pq.1.property h
      ∃ (φ : ConeSupport.E n → ℂ),
        ContDiff ℝ ↑(⊤ : ℕ∞) φ ∧
        HasCompactSupport φ ∧
        φ (pq.1.toEuclidean hp) ≠ 0 ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))
    )}

/-- A function `f : E → F` is positively homogeneous of degree `d : ℤ` if
`f (a • x) = a^d • f x` for every `a > 0` and every nonzero `x`. -/
def IsPositivelyHomogeneous (d : ℤ) (f : E → F) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (x : E), x ≠ 0 → f (a • x) = (a : ℝ) ^ d • f x

/-- The scaling continuous linear equivalence `E ≃L[ℝ] E` corresponding to a nonzero
scalar `a`; the action is `x ↦ a • x`. -/
noncomputable def scaleCLE (a : ℝ) (ha : a ≠ 0) : E ≃L[ℝ] E :=
  Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ E
open ConeSupport in

/-- Data structure packaging the inputs needed to define the `Css`-pairing
`⟨u₁, u₂⟩` used in Lemma 12.5: a notion of cone support `Css`, two cutoff
functions `ψ, ψ'` together with hypotheses that the relevant products have
empty `Css`, a recipe `toSchwartz` for upgrading such tempered distributions
to Schwartz functions, plus linearity and symmetry compatibilities. -/
structure CssPairingData {n : ℕ} (K₁ K₂ : Set (ConeSupport.E n)) where
  Css : 𝓢'(ConeSupport.E n, ℂ) → Set (ConeSupport.E n)
  ψ  : ConeSupport.E n → ℂ
  ψ' : ConeSupport.E n → ℂ
  toSchwartz : (u : 𝓢'(ConeSupport.E n, ℂ)) → Css u = ∅ →
    SchwartzMap (ConeSupport.E n) ℂ
  css_ψ_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ u) = ∅
  css_ψ_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ) u) = ∅
  css_ψ'_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ' u) = ∅
  css_ψ'_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ') u) = ∅
  css_diff_empty₂ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  css_diff_empty₁ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  linearity_mul : ∀ (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂)
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)),
    u₁ (toSchwartz _ (css_ψ_mul_empty u₂ h₂)) -
      u₁ (toSchwartz _ (css_ψ'_mul_empty u₂ h₂)) =
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂))
  linearity_compl : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)),
    u₂ (toSchwartz _ (css_ψ'_compl_mul_empty u₁ h₁)) -
      u₂ (toSchwartz _ (css_ψ_compl_mul_empty u₁ h₁)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))
  symmetry_eval : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂),
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))

variable {n : ℕ} {K₁ K₂ : Set (ConeSupport.E n)} (D : CssPairingData K₁ K₂)

open scoped SchwartzMap

/-- The `ψ`-pairing of `u₁` and `u₂` defined from `CssPairingData`:
`u₁(ψ·u₂) + u₂((1-ψ)·u₁)`, evaluated using the Schwartz representatives
produced by `toSchwartz`. -/
noncomputable def CssPairingData.pairingψ
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ_compl_mul_empty u₁ h₁))

/-- The `ψ'`-pairing of `u₁` and `u₂` from `CssPairingData`: the variant of
`pairingψ` using `ψ'` in place of `ψ`. The symmetry axioms in
`CssPairingData` ensure `pairingψ = pairingψ'`. -/
noncomputable def CssPairingData.pairingψ'
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ'_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ'_compl_mul_empty u₁ h₁))

end Lemma12_5

end WavefrontSet

open scoped SchwartzMap FourierTransform

namespace WavefrontSet

variable {n : ℕ}

/-- `ProductWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the pointwise product `u · v` of tempered distributions is
well-defined: for every base point `p` and every boundary frequency `ω`,
if `(p, ω) ∈ WFsc u` then `(p, -ω) ∉ WFsc v`. -/
def ProductWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (p ω : ClosedBall n), ‖ω.val‖ = 1 →
    (p, ω) ∈ WFsc u → (p, -ω) ∉ WFsc v

/-- `ConvolutionWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the convolution `u * v` of tempered distributions is well-defined:
for every boundary base direction `θ` and every frequency `q`, if `(θ, q) ∈ WFsc u`
then `(-θ, q) ∉ WFsc v`. Fourier-dual to `ProductWFscCondition`. -/
def ConvolutionWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (θ q : ClosedBall n), ‖θ.val‖ = 1 →
    (θ, q) ∈ WFsc u → (-θ, q) ∉ WFsc v

/-- Data witnessing that `u, v` can be convolved: a finite decomposition
`u = Σ uPart i + remainder`, `v = Σ vPart j` whose pairwise conic singular supports
satisfy the disjointness condition required for `ConeSupport.convolution_of_disjointCss`,
together with a remainder term `remainderConv` that handles the diagonal/leftover
contribution. -/
structure ConvolutionDecompData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  disjCss : ∀ i j : ι, ConeSupport.DisjointCssCondition (uPart i) (vPart j)
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

attribute [instance] ConvolutionDecompData.finι ConvolutionDecompData.decι

/-- The total convolution coming from a `ConvolutionDecompData`: sum of the
pairwise convolutions `convolution_of_disjointCss (uPart i) (vPart j)` plus the
remainder term. -/
structure ConicPartitionData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  angSupp : ι → Set (ConeSupport.Sphere n)
  angSupp_closed : ∀ i, IsClosed (angSupp i)
  css_uPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (uPart i) ⊆ angSupp i
  css_vPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (vPart i) ⊆ angSupp i
  angSupp_neg_disjoint : ∀ i j,
    Disjoint (angSupp i) (ConeSupport.negSet (angSupp j))
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

attribute [instance] ConicPartitionData.finι ConicPartitionData.decι
