import Lemma.Int.GeAbs_0
import Lemma.Int.GeSquare_0
import Lemma.Int.Le0Sub.is.Ge
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.LeSquareS.of.Le.Ge_0
import Lemma.Real.EqSqrtSquare.of.Ge_0
import Lemma.Real.LeSqrtS.of.Le.Ge_0
import Lemma.Set.LeAbs_MaxAbsS.of.In_Icc
open Int Nat Real Set


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h : x ∈ Icc a b) :
-- imply
  √((|a| ⊔ |b|)² - x²) ∈ Icc 0 (|a| ⊔ |b|) := by
-- proof
  set M := |a| ⊔ |b|
  have h_abs : |x| ≤ M := LeAbs_MaxAbsS.of.In_Icc h
  have hM : M ≥ 0 := ge_trans (GeMax.left |a| |b|) (GeAbs_0 a)
  have h_abs_nonneg : |x| ≥ 0 := GeAbs_0 x
  have h_sq : x² ≤ M² := by
    have h_abs_sq := LeSquareS.of.Le.Ge_0 h_abs_nonneg h_abs
    rwa [← sq_abs x]
  have h_sub_nonneg : M² - x² ≥ 0 := Le0Sub.of.Ge h_sq
  have h_sqrt_nonneg : √(M² - x²) ≥ 0 := GeSqrt_0 (M² - x²)
  have h_neg_sq : -x² ≤ 0 := neg_nonpos.mpr (GeSquare_0 x)
  have h_inner_le : M² - x² ≤ M² := by
    simpa [sub_eq_add_neg] using LeAddS.of.Le M² h_neg_sq
  have h_sqrt_le : √(M² - x²) ≤ M := by
    have h_sqrt_le_sq := LeSqrtS.of.Le.Ge_0 (GeSquare_0 M) h_inner_le
    rwa [EqSqrtSquare.of.Ge_0 hM] at h_sqrt_le_sq
  exact In_Icc.of.Le.Le h_sqrt_nonneg h_sqrt_le


-- created on 2018-07-08
