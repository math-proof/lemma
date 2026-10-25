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
import Def.RingTheory.GradedAlgebra.MultigradedHilbertSyzygy.Part14
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

section mgsyz_Stages

theorem mgsyz_projDim (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) (hk : k ≤ n) :
    CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded k).N) (n - k) := by
  induction k with
  | zero =>
      let : Module.Finite (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded 0).N :=
        Module.Finite.of_fg (mgsyz_stage K n M targetGraded 0).fg
      exact
        MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted.hilbert_syzygy
  | succ k ih =>
      let S := mgsyz_stage K n M targetGraded k
      let φ' := mgsyz_phiToN K n S
      let T := LinearMap.shortComplexKer φ'
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hprev := ih hk'
      change CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of (MvPolynomial (Fin n) K) ↥S.N) (n - k + 1) at hprev
      have hshort : T.ShortExact :=
        LinearMap.shortExact_shortComplexKer (mgsyz_phiToN_surjective K n S)
      have hfree : CategoryTheory.Projective T.X₂ := by
        exact ModuleCat.projective_of_free Finsupp.basisSingleOne
      have hker : CategoryTheory.HasProjectiveDimensionLT T.X₁
          (n - (k + 1) + 1) := by
        apply (hshort.hasProjectiveDimensionLT_X₃_iff (n - k - 1) hfree).mp
        simpa only [show n - k - 1 + 2 = n - k + 1 by omega] using hprev
      let e : T.X₁ ≅ ModuleCat.of (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded (k + 1)).N :=
        (LinearEquiv.ofEq _ _ (by
          simpa [T, φ', S, mgsyz_stage, mgsyz_next] using
            (mgsyz_phiToN_ker K n S))).toModuleIso
      let : CategoryTheory.HasProjectiveDimensionLT T.X₁
          (n - (k + 1) + 1) := hker
      change CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of (MvPolynomial (Fin n) K)
          ↥(mgsyz_stage K n M targetGraded (k + 1)).N)
        (n - (k + 1) + 1)
      exact CategoryTheory.hasProjectiveDimensionLT_of_iso e _

theorem mgsyz_stageN_projective (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Module.Projective (MvPolynomial (Fin n) K)
      ↥(mgsyz_stage K n M targetGraded n).N := by
  have hdim : CategoryTheory.HasProjectiveDimensionLE
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded n).N) 0 := by
    simpa using mgsyz_projDim K n M targetGraded n le_rfl
  have hprojective : CategoryTheory.Projective
      (ModuleCat.of (MvPolynomial (Fin n) K)
        ↥(mgsyz_stage K n M targetGraded n).N) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero _).mpr hdim
  exact (IsProjective.iff_projective _).mpr hprojective

theorem mgsyz_stage_succ_N_eq_bot (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    (mgsyz_stage K n M targetGraded (n + 1)).N = ⊥ := by
  let : Module.Projective (MvPolynomial (Fin n) K)
      ↥(mgsyz_stage K n M targetGraded n).N :=
    mgsyz_stageN_projective K n M targetGraded
  change LinearMap.ker
    (mgsyz_phi (K := K) n (mgsyz_stage K n M targetGraded n)) = ⊥
  exact mgsyz_ker_eq_bot_of_projective K n
    (mgsyz_stage K n M targetGraded n)

theorem mgsyz_minCard_eq_zero_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    mgsyz_minCard (K := K) n S = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  change Nat.find (mgsyz_coverProperty_exists (K := K) n S) ≤ 0
  apply Nat.find_min' (mgsyz_coverProperty_exists (K := K) n S)
  refine ⟨∅, by simp, ?_, ?_⟩
  · intro m hm
    simp at hm
  · simp [hS]

theorem mgsyz_cover_eq_empty_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    mgsyz_cover (K := K) n S = ∅ := by
  rw [← Finset.card_eq_zero, mgsyz_cover_card,
    mgsyz_minCard_eq_zero_of_N_eq_bot K n S hS]

theorem mgsyz_ι_isEmpty_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    IsEmpty (mgsyz_ι (K := K) n S) := by
  constructor
  intro j
  have hne : (mgsyz_cover (K := K) n S).Nonempty := ⟨j.1, j.2⟩
  rw [mgsyz_cover_eq_empty_of_N_eq_bot K n S hS] at hne
  exact Finset.not_nonempty_empty hne

theorem mgsyz_next_N_eq_bot_of_N_eq_bot (K : Type u) [Field K]
    (n : ℕ) (S : mgsyz_Stage K n) (hS : S.N = ⊥) :
    (mgsyz_next K n S).N = ⊥ := by
  let : IsEmpty (mgsyz_ι (K := K) n S) :=
    mgsyz_ι_isEmpty_of_N_eq_bot K n S hS
  change LinearMap.ker (mgsyz_phi (K := K) n S) = ⊥
  exact Submodule.eq_bot_of_subsingleton

theorem mgsyz_stage_N_eq_bot_of_succ_le (K : Type u) [Field K]
    (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (i : ℕ) (hi : n + 1 ≤ i) :
    (mgsyz_stage K n M targetGraded i).N = ⊥ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero =>
      simpa using mgsyz_stage_succ_N_eq_bot K n M targetGraded
  | succ d ih =>
      rw [Nat.add_succ]
      change (mgsyz_next K n
        (mgsyz_stage K n M targetGraded (n + 1 + d))).N = ⊥
      exact mgsyz_next_N_eq_bot_of_N_eq_bot K n _ (ih (by omega))

theorem mgsyz_ιk_isEmpty_of_lt (K : Type u) [Field K]
    (n : ℕ) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (i : ℕ) (hi : n < i) :
    IsEmpty (mgsyz_ιk K n M targetGraded i) :=
  mgsyz_ι_isEmpty_of_N_eq_bot K n (mgsyz_stage K n M targetGraded i)
    (mgsyz_stage_N_eq_bot_of_succ_le K n M targetGraded i
      (Nat.succ_le_iff.mpr hi))

theorem mgsyz_phik_range (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_phik K n M targetGraded k) =
      (mgsyz_stage K n M targetGraded k).N :=
  mgsyz_phi_range K n (mgsyz_stage K n M targetGraded k)

theorem mgsyz_phik_comp_succ (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    (mgsyz_phik K n M targetGraded (k + 1)).comp
      (mgsyz_phik K n M targetGraded (k + 2)) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : mgsyz_phik K n M targetGraded (k + 2) x ∈
      LinearMap.range (mgsyz_phik K n M targetGraded (k + 2)) :=
    (mgsyz_phik K n M targetGraded (k + 2)).mem_range_self x
  rw [mgsyz_phik_range] at hx
  exact LinearMap.mem_ker.mp hx

theorem mgsyz_phik_range_eq_ker (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] (k : ℕ) :
    LinearMap.range (mgsyz_phik K n M targetGraded (k + 1)) =
      LinearMap.ker (mgsyz_phik K n M targetGraded k) := by
  rw [mgsyz_phik_range]
  rfl

theorem mgsyz_phik_zero_surjective (K : Type u) [Field K] (n : ℕ)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M] (targetGraded : MultigradedPolynomialModule K n M)
    [Module.Finite (MvPolynomial (Fin n) K) M] :
    Function.Surjective (mgsyz_phik K n M targetGraded 0) := by
  rw [← LinearMap.range_eq_top, mgsyz_phik_range]
  rfl

end mgsyz_Stages
end
end MetaMathlibExt
