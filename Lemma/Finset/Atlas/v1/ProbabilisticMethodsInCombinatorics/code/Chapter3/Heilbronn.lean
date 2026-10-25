import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter3.Heilbronn
open Set Finset Heilbronn


namespace Heilbronn

/--
[intDetFin_cast_eq_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma intDetFin_cast_eq_vandermonde
  {p : ℕ}
  {a b c : Fin p} :
-- imply
  ((intDetFin a b c : ℤ) : ZMod p) = ((b.val : ZMod p) - a.val) * ((c.val : ZMod p) - a.val) * ((c.val : ZMod p) - b.val) := by
-- proof
  simp only [intDetFin]; push_cast; ring

end Heilbronn

namespace Heilbronn

/--
[fin_eq_of_zmod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma fin_eq_of_zmod_eq
  {p : ℕ}
  {a b : Fin p}
-- given
  (h : (a.val : ZMod p) = (b.val : ZMod p)) :
-- imply
  a = b :=
-- proof
  Fin.ext (ZMod.val_natCast_of_lt a.isLt ▸ ZMod.val_natCast_of_lt b.isLt ▸
    congr_arg ZMod.val h)

end Heilbronn

namespace Heilbronn

/--
[intDetFin_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma intDetFin_ne_zero
  {p : ℕ}
  {a b c : Fin p}
-- given
  (hp : Nat.Prime p)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c) :
-- imply
  intDetFin a b c ≠ 0 := by
-- proof
  intro h
  have h1 : ((intDetFin a b c : ℤ) : ZMod p) = 0 := by simp [h]
  rw [intDetFin_cast_eq_vandermonde] at h1
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr (fun heq => hab (fin_eq_of_zmod_eq b a heq).symm))
    (sub_ne_zero.mpr (fun heq => hac (fin_eq_of_zmod_eq c a heq).symm)))
    (sub_ne_zero.mpr (fun heq => hbc (fin_eq_of_zmod_eq c b heq).symm))) h1

end Heilbronn

namespace Heilbronn

/--
[cross_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma cross_product_formula
  {p : ℕ}
  {a b c : Fin p}
-- given
  (hp : 0 < p) :
-- imply
  ((parabolaPoint p b).1 - (parabolaPoint p a).1) * ((parabolaPoint p c).2 - (parabolaPoint p a).2) - ((parabolaPoint p b).2 - (parabolaPoint p a).2) * ((parabolaPoint p c).1 - (parabolaPoint p a).1) = (intDetFin a b c : ℝ) / (p : ℝ) ^ 2 := by
-- proof
  simp only [parabolaPoint, intDetFin]
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  field_simp; norm_cast

end Heilbronn

namespace Heilbronn

/--
[triangleArea_parabolaPoint_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma triangleArea_parabolaPoint_bound
  {p : ℕ}
  {a b c : Fin p}
-- given
  (hp : Nat.Prime p)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c) :
-- imply
  triangleArea (parabolaPoint p a) (parabolaPoint p b) (parabolaPoint p c) ≥ 1 / (2 * (p : ℝ) ^ 2) := by
-- proof
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  simp only [triangleArea]
  rw [cross_product_formula p hp.pos a b c, abs_div,
    abs_of_pos (show (0:ℝ) < (p:ℝ)^2 from by positivity), div_div]
  have hdet_abs : (1 : ℝ) ≤ |(intDetFin a b c : ℝ)| := by
    exact_mod_cast Int.one_le_abs (intDetFin_ne_zero hp a b c hab hac hbc)
  rw [ge_iff_le, show 2 * (p : ℝ) ^ 2 = (p : ℝ) ^ 2 * 2 from by ring]
  exact div_le_div_of_nonneg_right hdet_abs (by positivity)

end Heilbronn

namespace Heilbronn

/--
[parabolaPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma parabolaPoint_injective
  {p : ℕ}
-- given
  (hp : 0 < p) :
-- imply
  Function.Injective (parabolaPoint p) := by
-- proof
  intro i j hij
  simp only [parabolaPoint, Prod.mk.injEq] at hij
  have hpp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  have h1 := hij.1
  rw [div_eq_div_iff hpp hpp] at h1
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hpp h1))

end Heilbronn

namespace Heilbronn

/--
[parabolaPoint_mem_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma parabolaPoint_mem_unitSquare
  {p : ℕ}
  {i : Fin p}
-- given
  (hp : Nat.Prime p) :
-- imply
  parabolaPoint p i ∈ unitSquare := by
-- proof
  simp only [parabolaPoint, unitSquare, Set.mem_Icc, Prod.le_def]
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  exact ⟨⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hpp),
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hpp)⟩,
    ⟨(div_le_one hpp).mpr (by exact_mod_cast (Fin.is_lt i).le),
      (div_le_one hpp).mpr (by exact_mod_cast (Nat.mod_lt _ hp.pos).le)⟩⟩

end Heilbronn

namespace Heilbronn

/--
[heilbronn_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean)
-/
@[path]
lemma heilbronn_lower_bound
-- imply
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 → ∃ S : Finset (ℝ × ℝ), S.card = n ∧ (↑S : Set (ℝ × ℝ)) ⊆ unitSquare ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → x ≠ z → y ≠ z → triangleArea x y z ≥ c / (n : ℝ) ^ 2 := by
-- proof
  refine ⟨1 / 8, by norm_num, fun n hn => ?_⟩
  have hn_ne : n ≠ 0 := by omega
  have hn_pos : (0 : ℕ) < n := by omega
  obtain ⟨p, hp_prime, hnp, hp2n⟩ := Nat.bertrand n hn_ne
  have hpp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hnn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  set S_full := (Finset.univ : Finset (Fin p)).image (parabolaPoint p)
  have hcard_full : S_full.card = p := by
    rw [Finset.card_image_of_injective _ (parabolaPoint_injective hp_prime.pos),
      Finset.card_fin]
  obtain ⟨S, hS_sub, hS_card⟩ :=
    Finset.exists_subset_card_eq (hcard_full ▸ Nat.le_of_lt hnp)
  refine ⟨S, hS_card, ?_, ?_⟩
  · intro x hx
    have hxf : x ∈ S_full := hS_sub hx
    simp only [S_full, Finset.mem_image, Finset.mem_univ, true_and] at hxf
    obtain ⟨i, rfl⟩ := hxf
    exact parabolaPoint_mem_unitSquare hp_prime i
  · intro x hx y hy z hz hxy hxz hyz
    have hxf : x ∈ S_full := hS_sub hx
    have hyf : y ∈ S_full := hS_sub hy
    have hzf : z ∈ S_full := hS_sub hz
    simp only [S_full, Finset.mem_image, Finset.mem_univ, true_and] at hxf hyf hzf
    obtain ⟨i, rfl⟩ := hxf
    obtain ⟨j, rfl⟩ := hyf
    obtain ⟨k, rfl⟩ := hzf
    have hij : i ≠ j := fun h => hxy (congrArg _ h)
    have hik : i ≠ k := fun h => hxz (congrArg _ h)
    have hjk : j ≠ k := fun h => hyz (congrArg _ h)
    have h_area := triangleArea_parabolaPoint_bound hp_prime i j k hij hik hjk
    have h_bound : (1 : ℝ) / (2 * (p : ℝ) ^ 2) ≥ 1 / 8 / (n : ℝ) ^ 2 := by
      rw [ge_iff_le, div_div,
        div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * (n:ℝ)^2)
          (by positivity : (0:ℝ) < 2 * (p:ℝ)^2)]
      have h : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
      nlinarith [sq_nonneg ((p : ℝ)), sq_nonneg ((n : ℝ))]
    linarith

end Heilbronn


-- created on 2026-10-23
