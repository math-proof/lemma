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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part11
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

section mgsyz_MinimalCover

theorem mgsyz_phi_range (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) : LinearMap.range (mgsyz_phi (K := K) n S) = S.N := by
  rw [mgsyz_phi, Finsupp.range_linearCombination]
  change Submodule.span (MvPolynomial (Fin n) K)
    (Set.range (Subtype.val : mgsyz_ι (K := K) n S → S.W)) = S.N
  rw [Subtype.range_coe]
  exact mgsyz_cover_span (K := K) n S

theorem mgsyz_phi_degreeZero (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n) :
    letI : Module K (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    IsDegreeZero (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
      (mgsyz_phi (K := K) n S) := by
  apply mgsyz_linearCombination_isDegreeZero
  intro j
  exact mgsyz_delta_mem (K := K) n S j

end mgsyz_MinimalCover

section mgsyz_KernelConstantCoeff

theorem mgsyz_ker_constantCoeff (K : Type u) [Field K] (n : ℕ)
    (S : mgsyz_Stage K n)
    (q : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K)
    (hq : q ∈ LinearMap.ker (mgsyz_phi (K := K) n S))
    (j : mgsyz_ι (K := K) n S) :
    letI : Module K (mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    letI : DirectSum.Decomposition
        (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) :=
      mgsyz_freeDecomposition K (mgsyz_delta (K := K) n S);
    MvPolynomial.constantCoeff (q j) = 0 := by
  classical
  by_contra hconstant
  let β := mgsyz_delta (K := K) n S j
  let q' : mgsyz_ι (K := K) n S →₀ MvPolynomial (Fin n) K :=
    ((DirectSum.decompose
      (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) q) β :
      mgsyz_freeComponent K (mgsyz_delta (K := K) n S) β)
  have hq'ker : q' ∈ LinearMap.ker (mgsyz_phi (K := K) n S) :=
    @mgsyz_ker_graded K _ n _ _ _ _
      (Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)) _ _ _
      (mgsyz_freeGraded K (mgsyz_delta (K := K) n S)) S.gW
      (mgsyz_phi (K := K) n S) (mgsyz_phi_degreeZero K n S) q hq β
  have hq'component :
      q' ∈ mgsyz_freeComponent K (mgsyz_delta (K := K) n S) β :=
    ((DirectSum.decompose
      (mgsyz_freeComponent K (mgsyz_delta (K := K) n S)) q) β).property
  have hq'proj : q' = mgsyz_freeProj K (mgsyz_delta (K := K) n S) β q :=
    mgsyz_decompose_free_apply K (mgsyz_delta (K := K) n S) β q
  have hcoeff : (q' j).coeff 0 = (q j).coeff 0 := by
    rw [hq'proj, mgsyz_freeProj_apply]
    simp [β, mgsyz_natDegreeToInt_zero, MvPolynomial.coeff_monomial, eq_comm]
  have hcoeff_ne : (q' j).coeff 0 ≠ 0 := by
    rw [hcoeff]
    simpa [MvPolynomial.constantCoeff_eq] using hconstant
  let c := (q' j).coeff 0
  have hc : c ≠ 0 := hcoeff_ne
  have hsupport : (q' j).support = {0} := by
    ext a
    constructor
    · intro ha
      have hdeg := hq'component j a ha
      have hnat : natDegreeToInt a = 0 := by
        apply add_right_cancel (b := mgsyz_delta (K := K) n S j)
        simpa [β] using hdeg
      have ha0 := (mgsyz_natDegreeToInt_eq_zero_iff a).mp hnat
      simp [ha0]
    · intro ha
      have ha0 : a = 0 := by simpa using ha
      subst a
      exact MvPolynomial.mem_support_iff.mpr hc
  have hpolynomial : q' j = MvPolynomial.C c := by
    calc
      q' j = ∑ a ∈ (q' j).support,
          MvPolynomial.monomial a ((q' j).coeff a) := MvPolynomial.as_sum (q' j)
      _ = MvPolynomial.C c := by
        rw [hsupport]
        simp [c, MvPolynomial.monomial_zero']
  have hjSupport : j ∈ q'.support := by
    rw [Finsupp.mem_support_iff, hpolynomial]
    simp [hc]
  have hkernelEq : mgsyz_phi (K := K) n S q' = 0 := LinearMap.mem_ker.mp hq'ker
  rw [mgsyz_phi, Finsupp.linearCombination_apply] at hkernelEq
  change (∑ k ∈ q'.support, q' k • k.1) = 0 at hkernelEq
  have hsplit := Finset.add_sum_erase q'.support (fun k => q' k • k.1) hjSupport
  have hadd : q' j • j.1 + ∑ k ∈ q'.support.erase j, q' k • k.1 = 0 :=
    hsplit.trans hkernelEq
  rw [hpolynomial] at hadd
  have hsolve : MvPolynomial.C c • j.1 =
      -(∑ k ∈ q'.support.erase j, q' k • k.1) :=
    eq_neg_of_add_eq_zero_left hadd
  let t := (mgsyz_cover (K := K) n S).erase j.1
  have hsumSpan : (∑ k ∈ q'.support.erase j, q' k • k.1) ∈
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_erase]
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact ⟨fun h => hkj (Subtype.ext h), k.2⟩
  have hCcj : (MvPolynomial.C c : MvPolynomial (Fin n) K) • j.1 ∈
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    rw [hsolve]
    exact Submodule.neg_mem _ hsumSpan
  have hjSpan : j.1 ∈ Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) := by
    have hscaled := (Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W)).smul_mem
      (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) K) hCcj
    have hC : (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) K) * MvPolynomial.C c = 1 := by
      rw [← MvPolynomial.C_mul]
      simp [hc]
    simpa only [smul_smul, hC, one_smul] using hscaled
  have htSpan :
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) = S.N := by
    calc
      Submodule.span (MvPolynomial (Fin n) K) (t : Set S.W) =
          Submodule.span (MvPolynomial (Fin n) K) (insert j.1 (t : Set S.W)) :=
        (Submodule.span_insert_eq_span hjSpan).symm
      _ = Submodule.span (MvPolynomial (Fin n) K)
          (mgsyz_cover (K := K) n S : Set S.W) := by
        rw [← Finset.coe_insert, show insert j.1 t = mgsyz_cover (K := K) n S by
          exact Finset.insert_erase j.2]
      _ = S.N := mgsyz_cover_span (K := K) n S
  have htProperty : mgsyz_CoverProperty (K := K) n S t.card := by
    refine ⟨t, rfl, ?_, htSpan⟩
    intro m hm
    exact mgsyz_cover_homogeneous (K := K) n S m (Finset.erase_subset _ _ hm)
  have hle : mgsyz_minCard (K := K) n S ≤ t.card := by
    change Nat.find (mgsyz_coverProperty_exists (K := K) n S) ≤ t.card
    exact Nat.find_min' (mgsyz_coverProperty_exists (K := K) n S) htProperty
  have hlt : t.card < mgsyz_minCard (K := K) n S := by
    rw [← mgsyz_cover_card (K := K) n S]
    exact Finset.card_erase_lt_of_mem j.2
  exact (not_lt_of_ge hle hlt).elim

end mgsyz_KernelConstantCoeff
end
end MetaMathlibExt
