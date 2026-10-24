import Mathlib
import sympy.Basic
import sympy.atlas.Data.Set.Density
open Filter
open scoped Topology
open Set
open Finset Real
open HasIntDensity
open HasDensity
open Nat


namespace Set

/--
[partialDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma partialDensity_le_one
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact mod_cast Set.ncard_le_ncard <| Set.inter_subset_inter_left _ inter_subset_right

end Set

namespace Set

/--
[lowerDensity_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma lowerDensity_le_one
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  by_cases h : atTop (α := β) = ⊥
  · simp [h, Set.lowerDensity, Filter.liminf_eq]
  · have : (atTop (α := β)).NeBot := ⟨h⟩
    apply Real.sSup_le (fun x hx ↦ ?_) one_pos.le
    simpa using hx.mono fun y hy ↦ hy.trans (Set.partialDensity_le_one _ _ y)

end Set

namespace Set

/--
[lowerDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma lowerDensity_nonneg
  :
-- imply
  {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := by
-- proof
  rw [Set.lowerDensity, Filter.liminf_eq]
  exact (em _).elim (le_csSup · <| .of_forall fun _ ↦ by positivity)
    (Real.sSup_of_not_bddAbove · |>.ge)

end Set

namespace Set

/--
[intPartialDensity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma intPartialDensity_empty
  {N : ℕ} :
-- imply
  intPartialDensity (∅ : Set ℤ) N = 0 := by
-- proof
  simp [intPartialDensity]

end Set

namespace Set.HasIntDensity

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma empty
  :
-- imply
  HasIntDensity (∅ : Set ℤ) 0 := by
-- proof
  simp [HasIntDensity]

end Set.HasIntDensity

namespace Set.HasDensity

/--
[univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma univ
  [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] [Nontrivial β] :
-- imply
  (@univ β).HasDensity 1 := by
-- proof
  by_cases h : atTop (α := β) = ⊥
  · simp [h, HasDensity]
  · simp only [HasDensity, partialDensity, inter_self, univ_inter]
    let ⟨b, hb⟩ := Set.Iio_eventually_ncard_ne_zero β
    refine tendsto_const_nhds.congr' ?_
    exact (eventually_ge_atTop b).mono fun n hn ↦ (div_self <| mod_cast hb n hn).symm

end Set.HasDensity

namespace Set.HasDensity

/--
[univ_nat_hasDensity_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma univ_nat_hasDensity_one
  :
-- imply
  (@univ ℕ).HasDensity 1 :=
-- proof
  univ

end Set.HasDensity

namespace Set.HasDensity

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma empty
  :
-- imply
  HasIntDensity (∅ : Set ℤ) 0 := by
-- proof
  simpa [HasDensity, partialDensity] using tendsto_const_nhds

end Set.HasDensity

namespace Set.HasDensity

/--
[mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma mono
  :
-- imply
  {β : Type*} [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β]
    {S T : Set β} {αS αT : ℝ} [(atTop (α := by
-- proof
  rw [HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  filter_upwards [eventually_ge_atTop ⊥] with b hb
  apply div_le_div_of_nonneg_right
  grw [Set.ncard_le_ncard (inter_subset_inter_left _ (inter_subset_inter_left _ h))]
  exact Nat.cast_nonneg _

end Set.HasDensity

namespace Set.HasDensity

/--
[nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma nonneg
  [Preorder β] [LocallyFiniteOrderBot β] [(atTop : Filter β).NeBot]
  {S : Set β}
  {α : ℝ}
-- given
  (h : S.HasDensity α) :
-- imply
  0 ≤ α :=
-- proof
  le_of_tendsto_of_tendsto' empty h fun b => by simp [div_nonneg, partialDensity]
end Set.HasDensity
namespace Nat
open Set


namespace Set.Nat

/--
[hasDensity_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma hasDensity_even
  :
-- imply
  {n : ℕ | Even n}.HasDensity (1 / 2) := by
-- proof
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio_nat, one_div]
  have h {n : ℕ} (hn : 1 ≤ n) : (({n : ℕ | Even n} ∩ Iio n).ncard : ℝ) / n =
    if Even n then 2⁻¹ else (n + 1 : ℝ) /  n * 2⁻¹ := by
    split_ifs with h
    · rw [← image_mul_two_Iio_even h, ncard_image_of_injective _
      (mul_right_injective₀ (by simp)), Set.ncard_Iio_nat,
      cast_div_charZero (even_iff_two_dvd.mp h), cast_ofNat,
      div_div_cancel_left' <| cast_ne_zero.2 (by linarith)]
    · replace h : Even (n + 1) := by simpa [Nat.even_add', ← Nat.not_even_iff_odd]
      rw [← image_mul_two_Iio n, ncard_image_of_injective _
        (mul_right_injective₀ (by simp)), Set.ncard_Iio_nat,
        cast_div (even_iff_two_dvd.mp h) (by norm_num), cast_add]; ring
  refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (h hn).symm⟩)
    (Tendsto.if' tendsto_const_nhds ?_)
  replace h : Tendsto (fun (k : ℕ) => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using Tendsto.const_add (M := ℝ) _ tendsto_one_div_atTop_nhds_zero_nat
  simpa using Tendsto.mul_const _ <|
    Tendsto.congr' (eventually_atTop.2 ⟨1, fun k hk => by field_simp⟩) h

end Set.Nat

namespace Set.Nat

/--
[hasDensity_zero_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma hasDensity_zero_of_finite
  {S : Set ℕ}
-- given
  (h : S.Finite) :
-- imply
  S.HasDensity 0 := by
-- proof
  simp only [HasDensity, partialDensity, inter_univ, univ_inter, ncard_Iio_nat]
  have (n : ℕ) : ((S ∩ Set.Iio n).ncard : ℝ) / n ≤ S.ncard / n := by
    by_cases h₀ : n = 0; simp [h₀]
    exact div_le_div₀ (by simp) (by simpa using Set.ncard_inter_le_ncard_left _ _ h)
      (by simpa using n.pos_of_ne_zero h₀) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat _)
    (fun _ => div_nonneg (cast_nonneg _) (cast_nonneg _)) this

end Set.Nat

namespace Set.Nat

/--
[infinite_of_hasDensity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean)
-/
@[path]
lemma infinite_of_hasDensity_pos
  {S : Set ℕ}
  {α : ℝ}
-- given
  (h : S.HasDensity α)
  (hα : α ≠ 0) :
-- imply
  S.Infinite :=
-- proof
  mt hasDensity_zero_of_finite fun h' => hα (tendsto_nhds_unique h h')
end Nat
/-! ## Logarithmic Density -/
section LogarithmicDensity
open Finset Real



-- created on 2026-10-20
-- updated on 2026-10-23
