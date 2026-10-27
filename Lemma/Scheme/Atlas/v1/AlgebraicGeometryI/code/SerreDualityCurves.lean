import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityCurves.Part2
open SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology


namespace SerreDualityCurves

/--
[residueMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residueMap_apply
  {k : Type*}
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  residueMap k f = f (-1) :=
-- proof
  rfl

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residueMap_single_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residueMap_single_neg_one
  {k : Type*}
  [Field k]
  {a : k} :
-- imply
  residueMap k (Finsupp.single (-1 : ℤ) a) = a :=
-- proof
  Finsupp.single_eq_same

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residueMap_single_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residueMap_single_ne
  {k : Type*}
  [Field k]
  {n : ℤ}
  {a : k}
-- given
  (hn : n ≠ -1) :
-- imply
  residueMap k (Finsupp.single n a) = 0 :=
-- proof
  Finsupp.single_eq_of_ne (Ne.symm hn)

end SerreDualityCurves

namespace SerreDualityCurves

/--
[derivCoeff_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma derivCoeff_neg_one
  {k : Type*}
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  derivCoeff k f (-1) = 0 := by
-- proof
  simp [derivCoeff]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residue_of_exact_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residue_of_exact_zero
  {k : Type*}
  [Field k]
  {n : ℤ}
  {a : k} :
-- imply
  residueMap k (Finsupp.single (n - 1) ((↑n : k) * a)) = 0 := by
-- proof
  by_cases h : n - 1 = -1
  ·
    have hn : n = 0 := by omega
    subst hn; simp
  ·
    exact residueMap_single_ne k (n - 1) h ((↑n : k) * a)

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residue_annihilates_derivs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residue_annihilates_derivs
  {k : Type*}
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  derivCoeff k f (-1) = 0 :=
-- proof
  derivCoeff_neg_one k f

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residuePairing_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residuePairing_single
  {k : Type*}
  [Field k]
  {i j : ℤ}
  {a b : k} :
-- imply
  residuePairing k (Finsupp.single i a) (Finsupp.single j b) = if i + j = -1 then a * b else 0 := by
-- proof
  unfold residuePairing
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]
    by_cases hij : i + j = -1
    · have hj : j = -1 - i := by omega
      simp only [hij, ↓reduceIte]
      rw [hj, show (Finsupp.single (-1 - i) b : ℤ →₀ k) (-1 - i) = b from
        Finsupp.single_eq_same]
    · simp only [hij, ↓reduceIte]
      have hne : (-1 - i : ℤ) ≠ j := by omega
      rw [show (Finsupp.single j b : ℤ →₀ k) (-1 - i) = 0 from
        Finsupp.single_eq_of_ne hne]
      ring

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residuePairing_single_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residuePairing_single_comm
  {k : Type*}
  [Field k]
  {i j : ℤ}
  {a b : k} :
-- imply
  residuePairing k (Finsupp.single i a) (Finsupp.single j b) = residuePairing k (Finsupp.single j b) (Finsupp.single i a) := by
-- proof
  rw [residuePairing_single, residuePairing_single]
  by_cases h : i + j = -1
  · have : j + i = -1 := by linarith
    simp [h, this, mul_comm]
  · have : j + i ≠ -1 := by omega
    simp [h, this]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_chi_rank1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_chi_rank1
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 := by
-- proof
  rw [chi_eq_rr C 1 d, chi_eq_rr C 1 (C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_chi_O_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_chi_O_K
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) + C.χ (1, C.degK) = 0 := by
-- proof
  have := serre_duality_chi_rank1 C 0
  simp at this
  exact this

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_chi_rank_r](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_chi_rank_r
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) + C.χ (r, r * C.degK - d) = 0 := by
-- proof
  rw [chi_eq_rr C r d, chi_eq_rr C r (r * C.degK - d)]
  have hK := deg_canonical_eq_2g_sub_2 C
  rw [hK]; ring

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_numerical_from_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_numerical_from_chi
  {C : SmoothCompleteCurve}
-- given
  (d h0E h1E h0EK h1EK : ℤ)
  (hRR_E : h0E - h1E = C.χ (1, d))
  (hRR_EK : h0EK - h1EK = C.χ (1, C.degK - d))
  (hSD : h0E = h1EK) :
-- imply
  h1E = h0EK := by
-- proof
  have hsum := serre_duality_chi_rank1 C d
  linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[LocallyFreeSheaf.serreDual_deg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma LocallyFreeSheaf.serreDual_deg
  {C : SmoothCompleteCurve}
  {E : LocallyFreeSheaf C} :
-- imply
  E.serreDual.deg = ↑E.rk * C.degK - E.deg :=
-- proof
  rfl

end SerreDualityCurves

namespace SerreDualityCurves

/--
[LocallyFreeSheaf.serre_duality_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma LocallyFreeSheaf.serre_duality_chi
  {C : SmoothCompleteCurve}
  {E : LocallyFreeSheaf C} :
-- imply
  E.chi + E.serreDual.chi = 0 := by
-- proof
  show C.χ (↑E.rk, E.deg) + C.χ (↑E.rk, ↑E.rk * C.degK - E.deg) = 0
  exact serre_duality_chi_rank_r C ↑E.rk E.deg

end SerreDualityCurves

namespace SerreDualityCurves

/--
[LocallyFreeSheaf.serreDual_serreDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma LocallyFreeSheaf.serreDual_serreDual
  {C : SmoothCompleteCurve}
  {E : LocallyFreeSheaf C} :
-- imply
  E.serreDual.serreDual = E := by
-- proof
  ext <;> simp [serreDual]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[structureSheaf_serreDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma structureSheaf_serreDual
  {C : SmoothCompleteCurve} :
-- imply
  (structureSheaf C).serreDual = canonicalSheaf C := by
-- proof
  ext <;> simp [structureSheaf, canonicalSheaf, LocallyFreeSheaf.serreDual]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_O_K](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_O_K
  {C : SmoothCompleteCurve} :
-- imply
  (structureSheaf C).chi + (canonicalSheaf C).chi = 0 := by
-- proof
  rw [← structureSheaf_serreDual]
  exact (structureSheaf C).serre_duality_chi

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_P1_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_P1_dimension
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) :=
-- proof
  RiemannRoch.serre_duality_P1 k n

end SerreDualityCurves

namespace SerreDualityCurves

/--
[P1Curve_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma P1Curve_genus
-- imply
  P1Curve.g = 0 :=
-- proof
  rfl

end SerreDualityCurves

namespace SerreDualityCurves

/--
[P1Curve_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma P1Curve_degK
-- imply
  P1Curve.degK = -2 := by
-- proof
  simp [P1Curve, mkCurve]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[O_P1_serreDual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma O_P1_serreDual
  {n : ℤ} :
-- imply
  (O_P1 n).serreDual = O_P1 (-2 - n) := by
-- proof
  ext
  · simp [O_P1, LocallyFreeSheaf.serreDual]
  · simp [O_P1, LocallyFreeSheaf.serreDual, P1Curve_degK]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[chi_O_P1_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma chi_O_P1_duality
  {n : ℤ} :
-- imply
  (O_P1 n).chi + (O_P1 (-2 - n)).chi = 0 := by
-- proof
  rw [← O_P1_serreDual]
  exact (O_P1 n).serre_duality_chi

end SerreDualityCurves

namespace SerreDualityCurves

/--
[chi_O_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma chi_O_P1
  {n : ℤ} :
-- imply
  (O_P1 n).chi = n + 1 := by
-- proof
  show P1Curve.χ (1, n) = n + 1
  rw [chi_eq_rr P1Curve 1 n, P1Curve_genus]
  ring

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_P1_via_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_P1_via_shift
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Nonempty (((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k] ↥(CechH0 k (-2 - n))) :=
-- proof
  ⟨SerreDualityP1.serre_duality_P1 k n hn⟩

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_P1_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_P1_finrank_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = Module.finrank k ↥(CechH0 k (-2 - n)) :=
-- proof
  SerreDualityP1.serre_duality_finrank k n hn

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residuePairing_via_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residuePairing_via_shift
  {k : Type*}
  [Field k]
  {i : ℤ}
  {a : k}
  {g : ℤ →₀ k} :
-- imply
  residuePairing k (Finsupp.single i a) g = a * g (residueShift i) := by
-- proof
  unfold residuePairing residueShift
  by_cases ha : a = 0
  · simp [ha, Finsupp.single_zero, Finsupp.support_zero]
  · rw [Finsupp.support_single_ne_zero _ ha, Finset.sum_singleton, Finsupp.single_eq_same]

end SerreDualityCurves

namespace SerreDualityCurves

/--
[residue_shift_is_pairing_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma residue_shift_is_pairing_bijection
  {k : Type*}
  [Field k]
  {n : ℤ} :
-- imply
  residueShift '' (Set.Icc 0 n) = Set.Icc (-1 - n) (-1) := by
-- proof
  ext x
  simp only [Set.mem_image, Set.mem_Icc, residueShift]
  constructor
  · rintro ⟨y, ⟨hy0, hyn⟩, rfl⟩; constructor <;> omega
  · intro ⟨hx_lb, hx_ub⟩
    exact ⟨-1 - x, ⟨by omega, by omega⟩, by omega⟩

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_theorem
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 ∧ C.χ (1, d) = d + 1 - C.g :=
-- proof
  ⟨serre_duality_chi_rank1 C d, by rw [chi_eq_rr C 1 d]; ring⟩

end SerreDualityCurves

namespace SerreDualityCurves

/--
[genus_arithmetic_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma genus_arithmetic_eq_geometric
  {C : SmoothCompleteCurve}
-- given
  (ga gm h0_O h1_O h0_K h1_K : ℤ)
  (_hh0_O : h0_O = 1)
  (hga : ga = h1_O)
  (hgm : gm = h0_K)
  (hRR_O : h0_O - h1_O = C.χ (1, 0))
  (hRR_K : h0_K - h1_K = C.χ (1, C.degK))
  (hSD : h0_O = h1_K) :
-- imply
  ga = gm := by
-- proof
  have hchi := serre_duality_chi C
  linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_both_directions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_both_directions
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_E h0_EK h1_EK : ℤ)
  (hRR_E : h0_E - h1_E = C.χ (1, d))
  (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
  (hSD_0 : h0_E = h1_EK) :
-- imply
  h1_E = h0_EK := by
-- proof
  have hchi := serre_duality_chi_rank1 C d
  linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[riemann_roch_serre_form_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma riemann_roch_serre_form_general
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_D h0_KD : ℤ)
  (hRR : h0_D - h0_KD = C.χ (1, d)) :
-- imply
  h0_D - h0_KD = d + 1 - C.g := by
-- proof
  rw [chi_eq_rr C 1 d] at hRR; linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[riemann_inequality_from_RR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma riemann_inequality_from_RR
  {C : SmoothCompleteCurve}
-- given
  (d h0 h1 : ℤ)
  (hh1_nn : h1 ≥ 0)
  (hRR : h0 - h1 = d + 1 - C.g) :
-- imply
  h0 ≥ d + 1 - C.g := by
-- proof
linarith

end SerreDualityCurves

namespace SerreDualityCurves

/--
[deg_K_from_serre_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma deg_K_from_serre_duality
  {C : SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  deg_canonical_eq_2g_sub_2 C

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_chi_rank1_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_chi_rank1_dedekind
  [Field k]
  {C : DedekindCurve k}
  {d : ℤ} :
-- imply
  C.toSmoothCompleteCurve.χ (1, d) + C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK - d) = 0 :=
-- proof
  serre_duality_chi_rank1 C.toSmoothCompleteCurve d

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_chi_rank_r_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_chi_rank_r_dedekind
  [Field k]
  {C : DedekindCurve k}
  {r d : ℤ} :
-- imply
  C.toSmoothCompleteCurve.χ (r, d) + C.toSmoothCompleteCurve.χ (r, r * C.toSmoothCompleteCurve.degK - d) = 0 :=
-- proof
  serre_duality_chi_rank_r C.toSmoothCompleteCurve r d

end SerreDualityCurves

namespace SerreDualityCurves

/--
[serre_duality_canonical_h0_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityCurves.lean)
-/
@[path]
lemma serre_duality_canonical_h0_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.toSmoothCompleteCurve.χ (1, 0) + C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) = 0 :=
-- proof
  serre_duality_chi C.toSmoothCompleteCurve
end SerreDualityCurves



-- created on 2026-10-23
