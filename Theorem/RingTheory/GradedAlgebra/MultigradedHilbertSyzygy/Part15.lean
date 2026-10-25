/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedHilbertSyzygy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
import Mathlib.LinearAlgebra.Dimension.Finite
import Lemma.Int.GradedAlgebra.FiniteHomogeneousGenerators
import Def.RingTheory.Polynomial.HilbertSyzygy
import Lemma.Int.Polynomial.HilbertSyzygy
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part12
/-!
# Finite multigraded free resolutions over polynomial rings

Existence of a finite multigraded free resolution with finite homogeneous
basis types for every finitely generated module carrying the campaign
multigrading over `MvPolynomial (Fin n) K`.

Direct source for the existence claim: Hoffman–Wang,
*Regularity and Resolutions for Multigraded Modules*,
https://export.arxiv.org/e-print/math/0601101v1 lines 592-612, which states
that any finitely generated multigraded module has a finite free graded
resolution by finite direct sums of shifted copies of the polynomial algebra.

Motivation and multigraded Betti / Poincaré-series context: Braun–Davis,
*Antichain Simplices*, Journal of Integer Sequences 23 (2020),
https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex lines 856-876,
which records the Hilbert Syzygy consequence that the Poincaré series is a
polynomial over a polynomial ring. That JIS passage motivates this edge but
is not its proof source.

This edge claims finite termination only: no numerical bound `≤ n`, no
minimality or uniqueness, no base change, and no Poincaré-series conclusion.
-/


namespace MetaMathlibExt

universe u

open CategoryTheory MvPolynomial

noncomputable section

attribute [local instance] mgsyz_Stage.addCommGroup mgsyz_Stage.moduleR
  mgsyz_Stage.moduleK

section mgsyz_ProjectiveKernel

theorem mgsyz_phiToN_surjective (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : Function.Surjective (mgsyz_phiToN K n S) := by
  intro y
  have hy : y.1 ∈ LinearMap.range (mgsyz_phi (K := K) n S) := by
    rw [mgsyz_phi_range K n S]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem mgsyz_ker_eq_bot_of_projective (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n)
    [Module.Projective (MvPolynomial (Fin n) K) ↥S.N] :
    LinearMap.ker (mgsyz_phi (K := K) n S) = ⊥ := by
  classical
  let φ' := mgsyz_phiToN K n S
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property φ' LinearMap.id
    (mgsyz_phiToN_surjective K n S)
  let p : (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) →ₗ[
      MvPolynomial (Fin n) K] (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
    LinearMap.id - σ.comp φ'
  have hσ_apply (y : ↥S.N) : φ' (σ y) = y := by
    have h := congrArg (fun f => f y) hσ
    simpa using h
  have hpker (x : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :
      p x ∈ LinearMap.ker (mgsyz_phi (K := K) n S) := by
    rw [← mgsyz_phiToN_ker K n S, LinearMap.mem_ker]
    change φ' (x - σ (φ' x)) = 0
    rw [map_sub, hσ_apply]
    exact sub_self _
  have hpfix (x : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K)
      (hx : x ∈ LinearMap.ker (mgsyz_phi (K := K) n S)) : p x = x := by
    have hx' : x ∈ LinearMap.ker φ' := by
      rw [mgsyz_phiToN_ker K n S]
      exact hx
    have hx0 := LinearMap.mem_ker.mp hx'
    change x - σ (φ' x) = x
    rw [hx0]
    simp
  let I : Ideal (MvPolynomial (Fin n) K) :=
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K)
  have hle : LinearMap.ker (mgsyz_phi (K := K) n S) ≤
      I • LinearMap.ker (mgsyz_phi (K := K) n S) := by
    intro x hx
    have hrepr : (∑ j ∈ x.support,
        x j • Finsupp.single j (1 : MvPolynomial (Fin n) K)) = x := by
      calc
        (∑ j ∈ x.support, x j • Finsupp.single j (1 : MvPolynomial (Fin n) K)) =
            ∑ j ∈ x.support, Finsupp.single j (x j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finsupp.smul_single_one j (x j)
        _ = x := Finsupp.sum_single x
    rw [← hpfix x hx, ← hrepr, map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem_smul
    · rw [RingHom.mem_ker]
      exact mgsyz_ker_constantCoeff K n S x hx j
    · exact hpker (Finsupp.single j 1)
  have hfg : (LinearMap.ker (mgsyz_phi (K := K) n S)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨r, hrI, hrann⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (LinearMap.ker (mgsyz_phi (K := K) n S)) hfg hle
  have hrcc : MvPolynomial.constantCoeff r = 1 := by
    have hrzero := RingHom.mem_ker.mp hrI
    apply sub_eq_zero.mp
    simpa only [map_sub, map_one] using hrzero
  have hrne : r ≠ 0 := by
    intro hr
    rw [hr] at hrcc
    simp at hrcc
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply Finsupp.ext
  intro j
  have hcoord := congrArg (fun y => y j) (hrann x hx)
  change r * x j = 0 at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hrne

end mgsyz_ProjectiveKernel
end
end MetaMathlibExt
