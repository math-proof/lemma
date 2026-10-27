import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularElement
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Structure.v1.Atlas.TensorCategories.code.RegularElement
open Finset BigOperators FusionRing FusionRing.FPdimData


/--
[FPdim_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Prop_1_45_10.lean)
-/
@[path]
lemma FPdim_preserved
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty ι]
  [Nonempty κ]
  [HasPerronFrobeniusProperty ι]
  [HasPerronFrobeniusProperty κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {fpd_R : R.FPdimData}
  {fpd_S : S.FPdimData}
  {i : ι}
-- given
  (hM_nonneg : ∀ i l, (0 : ℤ) ≤ φ.M i l) :
-- imply
  fpd_R.d i = ∑ l : κ, (φ.M i l : ℝ) * fpd_S.d l := by
-- proof
  set χ : ι → ℝ := fun i => ∑ l : κ, (φ.M i l : ℝ) * fpd_S.d l with hχ_def
  have hχ_unit : χ R.unit = 1 := by
    simp only [hχ_def]
    conv_lhs => arg 2; ext l; rw [show (φ.M R.unit l : ℝ) = if l = S.unit then 1 else 0 from by
      rw [φ.map_unit]; split_ifs <;> simp]
    simp [fpd_S.d_unit]
  have hχ_mul : ∀ i j, χ i * χ j = ∑ k : ι, (R.N i j k : ℝ) * χ k := by
    intro i j
    have hmap_real : ∀ l : κ,
      (∑ p : κ, ∑ q : κ, (φ.M i p : ℝ) * (φ.M j q : ℝ) * (S.N p q l : ℝ)) =
      (∑ k : ι, (R.N i j k : ℝ) * (φ.M k l : ℝ)) := by
      intro l
      have h := φ.map_mul i j l
      have h' : (↑(Finset.univ.sum fun k => (R.N i j k : ℤ) * φ.M k l) : ℝ) =
        (↑(Finset.univ.sum fun p => Finset.univ.sum fun q =>
          φ.M i p * φ.M j q * (S.N p q l : ℤ)) : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      linarith
    have lhs_eq : χ i * χ j =
      ∑ l : κ, (∑ p : κ, ∑ q : κ,
        (φ.M i p : ℝ) * (φ.M j q : ℝ) * (S.N p q l : ℝ)) * fpd_S.d l := by
      show (∑ p, (φ.M i p : ℝ) * fpd_S.d p) * (∑ q, (φ.M j q : ℝ) * fpd_S.d q) = _
      rw [Finset.sum_mul_sum]
      simp_rw [show ∀ p q, (φ.M i p : ℝ) * fpd_S.d p * ((φ.M j q : ℝ) * fpd_S.d q) =
        (φ.M i p : ℝ) * (φ.M j q : ℝ) * (fpd_S.d p * fpd_S.d q) from by intros; ring]
      simp_rw [fpd_S.d_mul]
      simp_rw [Finset.mul_sum]
      simp_rw [show ∀ p q l, (φ.M i p : ℝ) * (φ.M j q : ℝ) *
        ((S.N p q l : ℝ) * fpd_S.d l) =
        (φ.M i p : ℝ) * (φ.M j q : ℝ) * (S.N p q l : ℝ) * fpd_S.d l from by intros; ring]
      conv_rhs =>
        arg 2; ext l; rw [Finset.sum_mul]; arg 2; ext p; rw [Finset.sum_mul]
      conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    have rhs_eq : ∑ k : ι, (R.N i j k : ℝ) * χ k =
      ∑ l : κ, (∑ k : ι, (R.N i j k : ℝ) * (φ.M k l : ℝ)) * fpd_S.d l := by
      conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
      conv_lhs => arg 2; ext k; arg 2; ext l; rw [← mul_assoc]
      rw [Finset.sum_comm]
      congr 1; ext l
      rw [← Finset.sum_mul]
    rw [lhs_eq, rhs_eq]
    congr 1; ext l; congr 1; exact hmap_real l
  have hχ_pos : ∀ i, χ i > 0 := by
    have hχ_nonneg : ∀ i, 0 ≤ χ i := by
      intro i; apply Finset.sum_nonneg; intro l _
      exact mul_nonneg (by exact_mod_cast hM_nonneg i l) (le_of_lt (fpd_S.d_pos l))
    intro i
    have hprod : 0 < χ i * χ (R.star i) := by
      rw [hχ_mul i (R.star i)]
      calc ∑ k, (R.N i (R.star i) k : ℝ) * χ k
        ≥ (R.N i (R.star i) R.unit : ℝ) * χ R.unit :=
          Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hχ_nonneg k))
            (Finset.mem_univ R.unit)
        _ = 1 := by rw [R.duality i (R.star i), if_pos rfl, Nat.cast_one, one_mul, hχ_unit]
        _ > 0 := one_pos
    obtain hi | hi := (hχ_nonneg i).eq_or_lt
    · exfalso; linarith [mul_eq_zero_of_left hi.symm (χ (R.star i))]
    · exact hi
  exact (fpDim_unique_character fpd_R χ hχ_unit hχ_pos hχ_mul i).symm

/--
[Proposition_1_45_10](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Prop_1_45_10.lean)
-/
@[path]
lemma Proposition_1_45_10
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty ι]
  [Nonempty κ]
  [HasPerronFrobeniusProperty ι]
  [HasPerronFrobeniusProperty κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {fpd_R : R.FPdimData}
  {fpd_S : S.FPdimData}
  {i : ι}
-- given
  (hM_nonneg : ∀ i l, (0 : ℤ) ≤ φ.M i l) :
-- imply
  fpd_R.d i = ∑ l : κ, (φ.M i l : ℝ) * fpd_S.d l :=
-- proof
  FPdim_preserved R S φ fpd_R fpd_S hM_nonneg i
section Regularity
variable [Nonempty ι] [Nonempty κ]
variable [HasPerronFrobeniusProperty ι] [HasPerronFrobeniusProperty κ]

/--
[map_mul_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Prop_1_45_10.lean)
-/
@[path]
lemma map_mul_real
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty ι]
  [Nonempty κ]
  [HasPerronFrobeniusProperty ι]
  [HasPerronFrobeniusProperty κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {a b : ι}
  {k' : κ} :
-- imply
  ∑ l : κ, ∑ Y : κ, (φ.M a l : ℝ) * (φ.M b Y : ℝ) * (S.N l Y k' : ℝ) = ∑ m : ι, (R.N a b m : ℝ) * (φ.M m k' : ℝ) := by
-- proof
  have h := φ.map_mul a b k'
  have h' : (↑(Finset.univ.sum fun m => (R.N a b m : ℤ) * φ.M m k') : ℝ) =
    (↑(Finset.univ.sum fun l => Finset.univ.sum fun Y =>
      φ.M a l * φ.M b Y * (S.N l Y k' : ℤ)) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/--
[fReg_eigenvec_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Prop_1_45_10.lean)
-/
@[path]
lemma fReg_eigenvec_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty ι]
  [Nonempty κ]
  [HasPerronFrobeniusProperty ι]
  [HasPerronFrobeniusProperty κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {fpd_R : R.FPdimData}
  {reg₁ : R.RegularElement fpd_R}
  {k : κ} :
-- imply
  ∑ Y : κ, (∑ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (S.N l Y k : ℝ)) * (∑ j : ι, reg₁.r j * (φ.M j Y : ℝ)) = (∑ X : ι, fpd_R.d X) * (∑ m : ι, reg₁.r m * (φ.M m k : ℝ)) := by
-- proof
  conv_lhs =>
    arg 2; ext Y
    rw [show (∑ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (S.N l Y k : ℝ)) *
      (∑ j : ι, reg₁.r j * (φ.M j Y : ℝ)) =
      ∑ j : ι, reg₁.r j * ((φ.M j Y : ℝ) *
        (∑ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (S.N l Y k : ℝ))) from by
      rw [mul_comm]; simp_rw [Finset.sum_mul]; congr 1; ext j; ring]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h_inner : ∀ j : ι,
    ∑ Y : κ, (φ.M j Y : ℝ) *
      (∑ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (S.N l Y k : ℝ)) =
    ∑ i : ι, ∑ m : ι, (R.N i j m : ℝ) * (φ.M m k : ℝ) := by
    intro j
    trans (∑ i : ι, ∑ l : κ, ∑ Y : κ,
      (φ.M i l : ℝ) * (φ.M j Y : ℝ) * (S.N l Y k : ℝ))
    · simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => arg 2; ext Y; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro Y _; ring
    · apply Finset.sum_congr rfl; intro i _
      exact map_mul_real R S φ i j k
  simp_rw [h_inner]
  simp only [Finset.mul_sum]
  simp_rw [show ∀ (x x_1 i : ι),
    reg₁.r x * ((R.N x_1 x i : ℝ) * (φ.M i k : ℝ)) =
    (R.N x_1 x i : ℝ) * reg₁.r x * (φ.M i k : ℝ) from by intros; ring]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x1; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x1; arg 2; ext x2; rw [← Finset.sum_mul]
  conv_lhs => arg 2; ext x1; arg 2; ext x2; rw [reg₁.left_absorb x1 x2]
  rw [Finset.sum_comm]
  congr 1; ext y
  simp_rw [show ∀ x : ι, fpd_R.d x * reg₁.r y * (φ.M y k : ℝ) =
    fpd_R.d x * (reg₁.r y * (φ.M y k : ℝ)) from by intros; ring]
  rw [← Finset.sum_mul]

/--
[reg2_eigenvec_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Prop_1_45_10.lean)
-/
@[path]
lemma reg2_eigenvec_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq κ]
  [Fintype κ]
  [Nonempty ι]
  [Nonempty κ]
  [HasPerronFrobeniusProperty ι]
  [HasPerronFrobeniusProperty κ]
  {R : FusionRing ι}
  {S : FusionRing κ}
  {φ : FusionRingHom R S}
  {fpd_R : R.FPdimData}
  {fpd_S : S.FPdimData}
  {reg₂ : S.RegularElement fpd_S}
  {k : κ}
-- given
  (hM_nonneg : ∀ i l, (0 : ℤ) ≤ φ.M i l) :
-- imply
  ∑ Y : κ, (∑ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (S.N l Y k : ℝ)) * reg₂.r Y = (∑ X : ι, fpd_R.d X) * reg₂.r k := by
-- proof
  conv_lhs =>
    arg 2; ext Y
    rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext l; arg 2; ext Y
    rw [mul_assoc]
  conv_lhs =>
    arg 2; ext l
    rw [← Finset.mul_sum]
  simp_rw [reg₂.left_absorb]
  simp_rw [show ∀ l : κ, (∑ i : ι, (φ.M i l : ℝ)) * (fpd_S.d l * reg₂.r k) =
    reg₂.r k * ((∑ i : ι, (φ.M i l : ℝ)) * fpd_S.d l) from by intro l; ring]
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  conv_rhs => arg 2; ext i; rw [FPdim_preserved R S φ fpd_R fpd_S hM_nonneg i]
  rw [Finset.sum_comm]
  congr 1; ext l
  rw [Finset.sum_mul]
end Regularity


-- created on 2026-10-23
