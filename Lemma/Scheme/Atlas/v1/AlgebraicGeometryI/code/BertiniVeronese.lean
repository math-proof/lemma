import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BertiniVeronese.Part3
open MvPolynomial Finset sets where a specified monomial coefficient is nonzero. -/ BertiniVeronese
open sets where a specified monomial coefficient is nonzero. -/


namespace BertiniVeronese

/--
[veroneseMonomialCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma veroneseMonomialCount_pos
  {n d : ℕ} :
-- imply
  0 < veroneseMonomialCount n d :=
-- proof
  Nat.choose_pos (Nat.le_add_left d n)

end BertiniVeronese

namespace BertiniVeronese

/--
[choose_two_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma choose_two_ge
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  n + 2 ≤ Nat.choose (n + 2) 2 := by
-- proof
  rw [Nat.choose_two_right]
  have h1 : n + 2 - 1 = n + 1 := by omega
  rw [h1]
  have h2 : 2 ≤ n + 1 := by omega
  have h3 : (n + 2) * 2 ≤ (n + 2) * (n + 1) := Nat.mul_le_mul_left (n + 2) h2
  have h4 : (n + 2) * 2 / 2 ≤ (n + 2) * (n + 1) / 2 := Nat.div_le_div_right h3
  simp at h4
  exact h4

end BertiniVeronese

namespace BertiniVeronese

/--
[choose_add_ge_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma choose_add_ge_succ
  {n d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  n + 1 ≤ Nat.choose (n + d) d := by
-- proof
  have hsym : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have h := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rwa [hnd] at h
  rw [← hsym]
  have h1 : Nat.choose (n + 1) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h2 : Nat.choose (n + 1) n = n + 1 := by
    have h := Nat.choose_symm (show n ≤ n + 1 by omega)
    have hnn : n + 1 - n = 1 := by omega
    rw [hnn] at h
    rw [← h, Nat.choose_one_right]
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[choose_add_ge_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma choose_add_ge_add_two
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  n + 2 ≤ Nat.choose (n + d) d := by
-- proof
  have hsym : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have h := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rwa [hnd] at h
  rw [← hsym]
  have h1 : Nat.choose (n + 2) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h2 : Nat.choose (n + 2) n = Nat.choose (n + 2) 2 := by
    have h := Nat.choose_symm (show n ≤ n + 2 by omega)
    have hnn : n + 2 - n = 2 := by omega
    rwa [hnn] at h
  have h3 := choose_two_ge n hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[veroneseEmbedDim_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma veroneseEmbedDim_ge
  {n d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  n ≤ veroneseEmbedDim n d := by
-- proof
  unfold veroneseEmbedDim
  have := choose_add_ge_succ n d hd
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[veronese_hypersurface_is_hyperplane](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma veronese_hypersurface_is_hyperplane
  {n d : ℕ} :
-- imply
  hypersurfaceParamDim n d = veroneseEmbedDim n d :=
-- proof
  rfl

end BertiniVeronese

namespace BertiniVeronese

/--
[bertini_veronese_dimension_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma bertini_veronese_dimension_count
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  smoothnessConditionCount n ≤ hypersurfaceParamDim n d := by
-- proof
  unfold smoothnessConditionCount hypersurfaceParamDim
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[incidence_variety_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma incidence_variety_dim
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  n + (hypersurfaceParamDim n d - smoothnessConditionCount n) < veroneseMonomialCount n d := by
-- proof
  unfold hypersurfaceParamDim smoothnessConditionCount veroneseMonomialCount
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[generic_hypersurface_smooth_codim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma generic_hypersurface_smooth_codim
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  n + (hypersurfaceParamDim n d - smoothnessConditionCount n) + 1 ≤ hypersurfaceParamDim n d := by
-- proof
  unfold hypersurfaceParamDim smoothnessConditionCount
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[discriminant_codimension_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma discriminant_codimension_pos
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  1 ≤ hypersurfaceParamDim n d - (n + (hypersurfaceParamDim n d - smoothnessConditionCount n)) := by
-- proof
  unfold hypersurfaceParamDim smoothnessConditionCount
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[generic_section_smooth_codim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma generic_section_smooth_codim
  {n d k : ℕ}
-- given
  (hd : 2 ≤ d)
  (hk : k ≤ n)
  (hn : 1 ≤ n) :
-- imply
  k + (hypersurfaceParamDim n d - (k + 1)) + 1 ≤ hypersurfaceParamDim n d := by
-- proof
  unfold hypersurfaceParamDim
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

namespace BertiniVeronese

/--
[veronese_bertini_summary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma veronese_bertini_summary
  {n d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  n + (Nat.choose (n + d) d - 1 - (n + 1)) < Nat.choose (n + d) d - 1 ∧ Nat.choose (n + d) d - 1 = veroneseEmbedDim n d ∧ n + 1 ≤ Nat.choose (n + d) d := by
-- proof
  refine ⟨?_, rfl, choose_add_ge_succ n d (by omega)⟩
  have := choose_add_ge_add_two n d hd hn
  omega

end BertiniVeronese

/--
[smooth_hypersurface_implies_smooth_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma smooth_hypersurface_implies_smooth_intersection
  {k : Type}
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {X : SmoothProjectiveVariety k n}
-- given
  (hf : IsSmooth_hypersurface f) :
-- imply
  IsSmooth_intersection_variety f X := by
-- proof
  intro x hx_ne _ hx_vanish
  by_contra h_all_vanish
  push Not at h_all_vanish
  exact absurd hx_vanish (hf x hx_ne h_all_vanish)

/--
[veroneseMonomialCount_ge_two_for_bertini](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean)
-/
@[path]
lemma veroneseMonomialCount_ge_two_for_bertini
  {n d : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  2 ≤ BertiniVeronese.veroneseMonomialCount n d := by
-- proof
  unfold BertiniVeronese.veroneseMonomialCount
  have : n + 1 ≤ Nat.choose (n + d) d := BertiniVeronese.choose_add_ge_succ n d hd
  omega
/-- Corollary 28 (a), Lec 22: over an algebraically closed field, the generic degree-`d`
hypersurface in `ℙⁿ` is smooth, for any `d ≥ 1` and `n ≥ 1`. -/


-- created on 2026-10-23
