import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LatticeBasics.Part2
open Matrix BigOperators LatticeBasics
open Submodule Set
open MeasureTheory Measure


namespace LatticeBasics

/--
[isUnimodular_iff_isUnit_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma isUnimodular_iff_isUnit_det
  [Fintype n]
  [DecidableEq n]
  {U : Matrix n n ℤ} :
-- imply
  IsUnimodular U ↔ IsUnit U.det := by
-- proof
  unfold IsUnimodular
  rw [Int.isUnit_iff]

end LatticeBasics

namespace LatticeBasics

/--
[isUnimodular_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma isUnimodular_inv
  [Fintype n]
  [DecidableEq n]
  {U : Matrix n n ℤ}
-- given
  (hU : IsUnimodular U) :
-- imply
  IsUnimodular U⁻¹ := by
-- proof
  rw [isUnimodular_iff_isUnit_det] at hU ⊢
  rwa [det_nonsing_inv]

end LatticeBasics

namespace LatticeBasics

/--
[isUnimodular_inv_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma isUnimodular_inv_iff
  [Fintype n]
  [DecidableEq n]
  {U : Matrix n n ℤ} :
-- imply
  IsUnimodular U ↔ IsUnimodular U⁻¹ := by
-- proof
  constructor
  · exact isUnimodular_inv U
  · intro hUinv
    rw [isUnimodular_iff_isUnit_det] at hUinv ⊢
    rw [det_nonsing_inv] at hUinv
    exact isUnit_ringInverse.mp hUinv

end LatticeBasics

namespace LatticeBasics

/--
[equivalent_bases_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma equivalent_bases_iff
  {n m : ℕ}
  {b₁ b₂ : Fin n → (Fin m → ℝ)}
-- given
  (hli₁ : LinearIndependent ℝ b₁)
  (hli₂ : LinearIndependent ℝ b₂) :
-- imply
  lattice n m b₁ hli₁ = lattice n m b₂ hli₂ ↔ ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnimodular U ∧ ∀ j, b₂ j = ∑ i, (U i j : ℤ) • b₁ i := by
-- proof
  simp only [lattice]
  have hli₁_ℤ : LinearIndependent ℤ b₁ := hli₁.restrict_scalars' ℤ
  constructor
  ·
    intro heq
    have hb₂_in_b₁ : ∀ j, b₂ j ∈ Submodule.span ℤ (Set.range b₁) := fun j => by
      rw [heq]; exact Submodule.subset_span (Set.mem_range_self j)
    have hb₁_in_b₂ : ∀ i, b₁ i ∈ Submodule.span ℤ (Set.range b₂) := fun i => by
      rw [← heq]; exact Submodule.subset_span (Set.mem_range_self i)
    choose U_coeff hU_eq using fun j =>
      (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp (hb₂_in_b₁ j)
    choose V_coeff hV_eq using fun i =>
      (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp (hb₁_in_b₂ i)
    let U : Matrix (Fin n) (Fin n) ℤ := fun i j => U_coeff j i
    let V : Matrix (Fin n) (Fin n) ℤ := fun i j => V_coeff j i
    have hUV : U * V = 1 := by
      have lindep := Fintype.linearIndependent_iffₛ.mp hli₁_ℤ
      ext k l
      simp only [Matrix.mul_apply, Matrix.one_apply, U, V]
      have key_eq : ∑ i, (fun i => ∑ j, U_coeff j i * V_coeff l j) i • b₁ i = b₁ l := by
        conv_rhs => rw [(hV_eq l).symm]
        simp_rw [fun j => (hU_eq j).symm]
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have triv_eq : ∑ i, (fun i => if i = l then (1 : ℤ) else 0) i • b₁ i = b₁ l := by
        simp [Finset.sum_ite_eq']
      exact lindep _ _ (key_eq.trans triv_eq.symm) k
    refine ⟨U, ?_, ?_⟩
    · rw [isUnimodular_iff_isUnit_det]
      exact Matrix.isUnit_det_of_right_inverse hUV
    · intro j; exact (hU_eq j).symm
  ·
    rintro ⟨U, hU_unimod, hrel⟩
    have hU_det_unit : IsUnit U.det := (isUnimodular_iff_isUnit_det U).mp hU_unimod
    apply Submodule.span_eq_span
    ·
      intro v hv
      obtain ⟨i, rfl⟩ := hv
      rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun (R := ℤ)]
      refine ⟨fun j => U⁻¹ j i, ?_⟩
      simp_rw [hrel]
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      suffices h : ∀ k, (∑ j, U⁻¹ j i * U k j) = if k = i then 1 else 0 by
        simp_rw [h, ite_smul, one_smul, zero_smul]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      intro k
      have : ∑ j, U k j * U⁻¹ j i = if k = i then 1 else 0 := by
        have hmul : (U * U⁻¹) k i = (1 : Matrix (Fin n) (Fin n) ℤ) k i := by
          rw [Matrix.mul_nonsing_inv _ hU_det_unit]
        simp only [Matrix.mul_apply, Matrix.one_apply] at hmul
        exact hmul
      convert this using 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    ·
      intro v hv
      obtain ⟨j, rfl⟩ := hv
      rw [SetLike.mem_coe]
      rw [hrel j]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end LatticeBasics

namespace LatticeBasics

/--
[latticeDet_eq_abs_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma latticeDet_eq_abs_det
  {n : ℕ}
  {b : Fin n → (Fin n → ℝ)}
-- given
  (_hli : LinearIndependent ℝ b) :
-- imply
  latticeDet n n b = := by
-- proof
  simp only [latticeDet]
  rw [det_mul, det_transpose, ← sq]
  exact Real.sqrt_sq_eq_abs _

end LatticeBasics

namespace LatticeBasics

/--
[basis_iff_fundamentalParallelepiped_inter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma basis_iff_fundamentalParallelepiped_inter
  {n : ℕ}
  {b : Fin n → (Fin n → ℝ)}
  {Λ : Submodule ℤ (Fin n → ℝ)}
-- given
  (hli : LinearIndependent ℝ b)
  (hBinΛ : ∀ i, b i ∈ Λ) :
-- imply
  lattice n n b hli = Λ ↔ fundamentalParallelepiped n n b ∩ (↑Λ : Set (Fin n → ℝ)) = {0} := by
-- proof
  constructor
  ·
    intro heq
    ext v
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, SetLike.mem_coe,
      fundamentalParallelepiped]
    constructor
    · rintro ⟨⟨x, hx_range, hx_eq⟩, hv_in_Λ⟩
      rw [← heq] at hv_in_Λ
      obtain ⟨y, hy_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp hv_in_Λ
      have hli_R := Fintype.linearIndependent_iffₛ.mp hli
      have h_eq_coeffs : ∀ i, x i = (y i : ℤ) := by
        have heq_sums : ∑ i, x i • b i = ∑ i, (↑(y i) : ℝ) • b i := by
          rw [hx_eq, ← hy_eq]
          congr 1; ext1 i; simp only [Int.cast_smul_eq_zsmul]
        exact hli_R x (fun i => (↑(y i) : ℝ)) heq_sums
      have hx_zero : ∀ i, x i = 0 := by
        intro i
        have h1 := (hx_range i).1
        have h2 := (hx_range i).2
        rw [h_eq_coeffs i] at h1 h2
        have hge : (0 : ℤ) ≤ y i := by exact_mod_cast h1
        have hlt : (y i : ℤ) < 1 := by exact_mod_cast h2
        have : y i = 0 := by omega
        simp [h_eq_coeffs i, this]
      rw [← hx_eq]; simp [hx_zero]
    · intro hv; subst hv
      exact ⟨⟨0, fun i => ⟨le_refl _, zero_lt_one⟩, by simp⟩, Λ.zero_mem⟩
  ·
    intro hinter
    have hlattice_le : lattice n n b hli ≤ Λ :=
      Submodule.span_le.mpr (fun v ⟨i, hi⟩ => hi ▸ hBinΛ i)
    apply le_antisymm hlattice_le
    intro v hv_in_Λ
    by_cases hn : n = 0
    · subst hn
      have hv_in_P : v ∈ fundamentalParallelepiped 0 0 b :=
        ⟨Fin.elim0, fun i => i.elim0, by simp [Finset.univ_eq_empty]; ext i; exact i.elim0⟩
      have hv_in_inter : v ∈ fundamentalParallelepiped 0 0 b ∩ (↑Λ : Set (Fin 0 → ℝ)) :=
        ⟨hv_in_P, hv_in_Λ⟩
      rw [hinter] at hv_in_inter
      rw [Set.mem_singleton_iff.mp hv_in_inter]
      exact Submodule.zero_mem _
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hne : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
      have hspan_top : Submodule.span ℝ (Set.range b) = ⊤ :=
        LinearIndependent.span_eq_top_of_card_eq_finrank hli (by simp)
      have hv_in_span : v ∈ Submodule.span ℝ (Set.range b) := by rw [hspan_top]; trivial
      obtain ⟨c, hc_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hv_in_span
      let c' : Fin n → ℝ := fun i => Int.fract (c i)
      have hc'_range : ∀ i, 0 ≤ c' i ∧ c' i < 1 := fun i =>
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      let v' := ∑ i, c' i • b i
      have hv'_in_P : v' ∈ fundamentalParallelepiped n n b :=
        ⟨c', hc'_range, rfl⟩
      have hv'_eq : v' = v - ∑ i, (↑⌊c i⌋ : ℝ) • b i := by
        simp only [v', c', Int.fract, sub_smul, Finset.sum_sub_distrib, hc_eq]
      have hfloor_in_Λ : ∑ i, (⌊c i⌋ : ℤ) • b i ∈ Λ :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hBinΛ i)
      have hv'_in_Λ : v' ∈ Λ := by
        rw [hv'_eq]
        have hcast : (∑ i, (↑⌊c i⌋ : ℝ) • b i) = ∑ i, (⌊c i⌋ : ℤ) • b i := by
          congr 1; ext1 i; simp only [Int.cast_smul_eq_zsmul]
        rw [hcast]
        exact Submodule.sub_mem _ hv_in_Λ hfloor_in_Λ
      have hv'_in_inter : v' ∈ fundamentalParallelepiped n n b ∩ (↑Λ : Set (Fin n → ℝ)) :=
        ⟨hv'_in_P, hv'_in_Λ⟩
      rw [hinter] at hv'_in_inter
      have hv'_zero : v' = 0 := Set.mem_singleton_iff.mp hv'_in_inter
      have hc_int : ∀ i, c i = ↑(⌊c i⌋ : ℤ) := by
        intro i
        have hli_R := Fintype.linearIndependent_iffₛ.mp hli
        have hsum_eq : ∑ j, c' j • b j = ∑ j, (0 : ℝ) • b j := by
          simp only [zero_smul, Finset.sum_const_zero]
          exact hv'_zero
        have hc'_zero : c' i = 0 := hli_R c' (fun _ => 0) hsum_eq i
        simp only [c', Int.fract] at hc'_zero
        linarith
      rw [show lattice n n b hli = Submodule.span ℤ (Set.range b) from rfl]
      rw [Submodule.mem_span_range_iff_exists_fun (R := ℤ)]
      refine ⟨fun i => ⌊c i⌋, ?_⟩
      rw [← hc_eq]
      congr 1; ext1 i
      rw [hc_int i]; simp only [Int.cast_smul_eq_zsmul]
open MeasureTheory Measure

end LatticeBasics

namespace LatticeBasics

/--
[blichfeldt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean)
-/
@[path]
lemma blichfeldt
  {n : ℕ}
  [NeZero n]
  {b : Fin n → (Fin n → ℝ)}
  {S : Set (Fin n → ℝ)}
-- given
  (hli : LinearIndependent ℝ b)
  (hS : MeasurableSet S)
  (hvol : ENNReal.ofReal (latticeDet n n b) < volume S) :
-- imply
  ∃ z₁ z₂ : Fin n → ℝ, z₁ ∈ S ∧ z₂ ∈ S ∧ z₁ ≠ z₂ ∧ z₁ - z₂ ∈ lattice n n b hli := by
-- proof
  have hdet_eq : latticeDet n n b = |(Matrix.of b).det| := latticeDet_eq_abs_det n b hli
  rw [hdet_eq] at hvol
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hBcoe : (↑B : Fin n → (Fin n → ℝ)) = b :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hvol_fund : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal |(Matrix.of b).det| := by
    rw [ZSpan.volume_fundamentalDomain B]
    congr 2
    exact congrArg (fun f => (Matrix.of f).det) hBcoe
  have hspan_eq : Submodule.span ℤ (range (↑B : Fin n → (Fin n → ℝ))) =
    Submodule.span ℤ (range b) := by
    rw [hBcoe]
  haveI : Countable (Submodule.span ℤ (range (↑B : Fin n → (Fin n → ℝ)))).toAddSubgroup := by
    change Countable ↥(Submodule.span ℤ (range (↑B : Fin n → (Fin n → ℝ))))
    infer_instance
  have hfund : IsAddFundamentalDomain
    (Submodule.span ℤ (range (↑B : Fin n → (Fin n → ℝ)))).toAddSubgroup
    (ZSpan.fundamentalDomain B) volume :=
    ZSpan.isAddFundamentalDomain' B volume
  have hvol' : volume (ZSpan.fundamentalDomain B) < volume S := by
    rw [hvol_fund]; exact hvol
  obtain ⟨x, y, hxy, hnd⟩ :=
    exists_pair_mem_lattice_not_disjoint_vadd hfund hS.nullMeasurableSet hvol'
  rw [Set.not_disjoint_iff] at hnd
  obtain ⟨p, hpx, hpy⟩ := hnd
  rw [Set.mem_vadd_set] at hpx hpy
  obtain ⟨s₁, hs₁, hps₁⟩ := hpx
  obtain ⟨s₂, hs₂, hps₂⟩ := hpy
  have heq : (x : Fin n → ℝ) + s₁ = (y : Fin n → ℝ) + s₂ := by
    have : (x : Fin n → ℝ) +ᵥ s₁ = (y : Fin n → ℝ) +ᵥ s₂ := hps₁.trans hps₂.symm
    simpa [vadd_eq_add] using this
  refine ⟨s₁, s₂, hs₁, hs₂, ?_, ?_⟩
  ·
    intro h_eq
    apply hxy
    have : (x : Fin n → ℝ) = (y : Fin n → ℝ) := by
      have h := heq; rw [h_eq] at h; exact add_right_cancel h
    exact Subtype.ext this
  ·
    show s₁ - s₂ ∈ Submodule.span ℤ (range b)
    have hsub : s₁ - s₂ = (↑y : Fin n → ℝ) - (↑x : Fin n → ℝ) := by
      linear_combination heq
    rw [hsub, ← hspan_eq]
    exact (Submodule.span ℤ (range (↑B : Fin n → (Fin n → ℝ)))).sub_mem y.2 x.2

end LatticeBasics


-- created on 2026-10-23
