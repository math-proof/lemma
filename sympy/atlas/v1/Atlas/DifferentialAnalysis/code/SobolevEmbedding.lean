/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped ZeroAtInfty
open MeasureTheory Filter Topology

noncomputable section

namespace SobolevEmbedding

/-- A (strong) Sobolev space `H^m` on `ℝ^n`: smooth functions `u : ℝ^n → ℂ` of class
`C^m` such that each iterated Fréchet derivative `D^j u` (for `j ≤ m`) is square
integrable with respect to Lebesgue measure. -/
structure SobolevSpace (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  contDiff_toFun : ContDiff ℝ (m : ℕ∞) toFun
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpace n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpace.toFun⟩

/-- `H^m ⊂ H^{m'}` whenever `m' ≤ m`: lower the Sobolev order of an element by
restricting the derivative-integrability hypothesis. -/
def SobolevSpace.toLowerOrder {n : ℕ} {m m' : ℕ} (hle : m' ≤ m)
    (u : SobolevSpace n m) : SobolevSpace n m' where
  toFun := u.toFun
  contDiff_toFun := u.contDiff_toFun.of_le (Nat.cast_le.mpr hle)
  iteratedFDeriv_memLp j hj := u.iteratedFDeriv_memLp j (le_trans hj hle)


set_option synthInstance.maxHeartbeats 80000 in
/-- For `u ∈ H^m` and a coordinate direction `j`, the partial derivative
`∂_j u` has all iterated derivatives up to order `m-1` in `L^2`. This is the
key technical lemma used to define `SobolevSpace.partialDeriv`. -/
theorem partialDeriv_iteratedFDeriv_memLp {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) (i : ℕ) (hi : i ≤ m - 1) :
    MemLp (fun x => iteratedFDeriv ℝ i
      (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by

  have hmem := u.iteratedFDeriv_memLp (i + 1) (by omega)

  have hcd_fderiv : ContDiff ℝ (↑i : ℕ∞) (fderiv ℝ u.toFun) := by
    apply u.contDiff_toFun.fderiv_right
    norm_cast; omega

  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ i
        (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x‖ ≤
      ‖EuclideanSpace.single j (1 : ℝ)‖ *
        ‖iteratedFDeriv ℝ (i + 1) u.toFun x‖ := by
    intro x
    have h1 := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ u.toFun) (c := EuclideanSpace.single j (1 : ℝ)) (x := x)
      hcd_fderiv.contDiffAt (N := (↑i : ℕ∞)) (le_refl _)
    rw [norm_iteratedFDeriv_fderiv] at h1
    exact h1

  exact hmem.of_le_mul
    ((hcd_fderiv.clm_apply contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- Partial derivative `∂_j u` as an element of `H^{m-1}`, given `u ∈ H^m`. -/
def SobolevSpace.partialDeriv {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) : SobolevSpace n (m - 1) where
  toFun := fun x => fderiv ℝ u.toFun x (EuclideanSpace.single j 1)
  contDiff_toFun := by
    have hle : ((↑(m - 1) : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((↑m : ℕ∞) : WithTop ℕ∞) := by
      norm_cast; exact (Nat.sub_add_cancel hm).le
    exact (ContDiff.fderiv_right u.contDiff_toFun hle).clm_apply contDiff_const
  iteratedFDeriv_memLp i hi := partialDeriv_iteratedFDeriv_memLp hm u j i hi


set_option synthInstance.maxHeartbeats 80000 in

/-- Iterate the partial derivative in direction `j` exactly `k` times, mapping
`H^m` into `H^{m-k}`. -/
def SobolevSpace.iteratedPartialDeriv {n : ℕ} {m : ℕ}
    (j : Fin n) : (k : ℕ) → (hk : k ≤ m) → SobolevSpace n m → SobolevSpace n (m - k)
  | 0, _, u => u.toLowerOrder (by omega)
  | k + 1, hk, u =>
    let v := SobolevSpace.iteratedPartialDeriv j k (by omega) u
    (v.partialDeriv (by omega) j).toLowerOrder (by omega)

/-- Sobolev embedding into `C_0^k`: the iterated derivative `D^j f` vanishes at
infinity (cocompactly) when `f` has `H^m` regularity above the Sobolev threshold. -/
structure SobolevSpaceWeak (n : ℕ) (m : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  iteratedFDeriv_memLp (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j toFun x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))

/-- Treat a weak Sobolev space element as the underlying function `ℝ^n → ℂ`. -/
instance {n m : ℕ} : CoeFun (SobolevSpaceWeak n m) (fun _ => EuclideanSpace ℝ (Fin n) → ℂ) :=
  ⟨SobolevSpaceWeak.toFun⟩

/-- The (strong) Sobolev space embeds into the weak Sobolev space by forgetting
the a priori smoothness. -/
def SobolevSpace.toWeak {n m : ℕ} (u : SobolevSpace n m) : SobolevSpaceWeak n m where
  toFun := u.toFun
  iteratedFDeriv_memLp := u.iteratedFDeriv_memLp


/-- **Sobolev embedding** (Melrose Cor. 10.3): if `k ≤ m` and `n < 2(m - k)`,
then every weak Sobolev function `u ∈ H^m` is (a.e. equal to) a `C^k` function
whose derivatives of order `≤ k` all vanish at infinity, i.e. `H^m ↪ C_0^k`. -/
structure SobolevInfty (n : ℕ) where
  mem_sobolev : ∀ m : ℕ, SobolevSpace n m
  consistent : ∀ m₁ m₂ : ℕ, (mem_sobolev m₁).toFun = (mem_sobolev m₂).toFun

/-- Base case `k = 0` of the Sobolev embedding: `H^m ⊂ C_0` when `m > n/2`. -/
end SobolevEmbedding

open scoped SchwartzMap

namespace SchwartzRepresentation

variable {n : ℕ}

/-- Order `|α| = α₁ + ⋯ + α_n` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- The finite set of all multi-indices `α : Fin n → ℕ` with `|α| ≤ m`. -/
def multiIndicesBall (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (m + 1))).filter
    (fun α => multiIndexOrder α ≤ m)

/-- The monomial `x^α = ∏ x_i^{α_i}` viewed as a complex-valued function on
`ℝ^n`. -/
def monomial (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∏ i : Fin n, (↑(x i) : ℂ) ^ (α i)

/-- Iterate the line derivative `∂_{x_j}` exactly `k` times on a Schwartz
function. -/
def iterSchwartzDerivCoord (j : Fin n) (k : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)))^[k] φ

/-- The multi-index partial derivative `∂^β` on Schwartz functions, defined by
iteratively applying coordinate derivatives in each direction `j` exactly
`β j` times. -/
def iterSchwartzDeriv (β : Fin n → ℕ) (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j ψ => iterSchwartzDerivCoord j (β j) ψ) φ

section SchwartzLpEmbedding

open MeasureTheory

/-- Every Schwartz derivative `∂^α φ` belongs to `L^2`. -/
theorem schwartzDerivMemLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemLp ((iterSchwartzDeriv α φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
      EuclideanSpace ℝ (Fin n) → ℂ) 2 volume :=
  (iterSchwartzDeriv α φ).memLp 2

/-- Map a Schwartz function `φ` to the `L^2` equivalence class of `∂^α φ`. -/
noncomputable def schwartzToLp (n : ℕ) (α : Fin n → ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (schwartzDerivMemLp n α φ).toLp _

/-- Pairing `⟨f, φ⟩ = ∫ f(x) · φ(x) dx` of a `C_0` function `f` against a
Schwartz function `φ`, used to express tempered distributions of the form
arising in the Schwartz representation theorem. -/
def c0SchwartzPairing
    (f : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : ℂ :=
  ∫ x, f x * φ x


set_option maxHeartbeats 1600000 in

/-- Joint `L^2 → C_0` decomposition: a finite sum `∑_α ∫ g_α · ∂^α φ` over
`|α| ≤ m` of `L^2`-functions can be rewritten as `∑_γ c0SchwartzPairing (v γ) (∂^γ φ)`
with each `v γ` a `C_0` function. -/
def multiIndicesBelow (n : ℕ) (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (γ i + 1))
