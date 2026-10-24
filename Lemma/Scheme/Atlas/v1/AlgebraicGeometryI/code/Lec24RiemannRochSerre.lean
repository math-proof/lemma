import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec24RiemannRochSerre
open Lec24 Lec24.SmoothCompleteCurveWithSheaves


namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[riemann_roch](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma riemann_roch
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf} :
-- imply
  ((X.data E).h0 : ℤ) - ((X.data E).h1 : ℤ) = (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) := by
-- proof
  have hchi := X.chi_determined_by_rk_deg E
  rw [X.structureSheaf_h0, X.structureSheaf_h1] at hchi
  push_cast at hchi ⊢
  linarith

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[chi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma chi_eq
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf} :
-- imply
  X.chi E = (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) :=
-- proof
  X.riemann_roch E

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[chi_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma chi_structure
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  X.chi X.structureSheaf = 1 - (X.genus : ℤ) := by
-- proof
  rw [chi_eq, X.structureSheaf_deg, X.structureSheaf_rk]; push_cast; ring

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24

/--
[serre_duality_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma serre_duality_dimension
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf} :
-- imply
  (X.data E).h0 = (X.data (X.serreDual E)).h1 :=
-- proof
  X.serre_duality E

end Lec24

namespace Lec24

/--
[serre_duality_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma serre_duality_reverse
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf} :
-- imply
  (X.data E).h1 = (X.data (X.serreDual E)).h0 := by
-- proof
  have hsd := serre_duality_dimension X (X.serreDual E)
  rwa [X.serreDual_involutive] at hsd

end Lec24

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[arithmetic_eq_geometric_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma arithmetic_eq_geometric_genus
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  (X.data X.canonicalSheaf).h0 = X.genus := by
-- proof
  have hsd := serre_duality_dimension X X.canonicalSheaf
  rw [X.serreDual_canonical] at hsd
  rw [hsd, X.structureSheaf_h1]

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[h1_canonical_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma h1_canonical_eq_one
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  (X.data X.canonicalSheaf).h1 = 1 := by
-- proof
  have hsd := serre_duality_dimension X X.structureSheaf
  rw [X.serreDual_structure] at hsd
  rwa [X.structureSheaf_h0] at hsd

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[deg_canonical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma deg_canonical_eq
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  X.degK = 2 * (X.genus : ℤ) - 2 := by
-- proof
  have hRR := X.riemann_roch X.canonicalSheaf
  rw [X.canonicalSheaf_deg, X.canonicalSheaf_rk,
    X.arithmetic_eq_geometric_genus, X.h1_canonical_eq_one] at hRR
  push_cast at hRR ⊢; omega

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[riemann_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma riemann_form
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf} :
-- imply
  ((X.data E).h0 : ℤ) - ((X.data (X.serreDual E)).h0 : ℤ) = (X.data E).deg + (X.data E).rk * (1 - (X.genus : ℤ)) := by
-- proof
  have hsd_rev := serre_duality_reverse X E
  have hRR := X.riemann_roch E
  have : ((X.data (X.serreDual E)).h0 : ℤ) = ((X.data E).h1 : ℤ) := by
    exact_mod_cast hsd_rev.symm
  linarith

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[h0_high_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma h0_high_degree
  {X : SmoothCompleteCurveWithSheaves}
  {E : X.Sheaf}
-- given
  (hrk : (X.data E).rk = 1)
  (hvanish : (X.data (X.serreDual E)).h0 = 0) :
-- imply
  ((X.data E).h0 : ℤ) = (X.data E).deg + 1 - (X.genus : ℤ) := by
-- proof
  have hsd_rev := serre_duality_reverse X E
  have hRR := X.riemann_roch E
  rw [hsd_rev, hvanish] at hRR
  rw [hrk] at hRR
  push_cast at hRR ⊢
  linarith

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24

/--
[classOf_in_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma classOf_in_range
  {X : SmoothCurveK0Data}
  {F : X.CohSheaf}
-- given
  (torsion_decomp : ∀ F : X.CohSheaf, X.rank F = 0 → ∃ (n : ℤ), K0Coh.classOf X F = n • K0Coh.classOf X X.O_x)
  (rank_reduction : ∀ F : X.CohSheaf, 0 < X.rank F → ∃ (d : ℤ) (Q : X.CohSheaf), X.rank Q < X.rank F ∧ K0Coh.classOf X F = K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x + K0Coh.classOf X Q) :
-- imply
  K0Coh.classOf X F ∈ (rankDegToK0 X).range := by
-- proof
  have : ∀ n : ℕ, ∀ G : X.CohSheaf, X.rank G = n →
    K0Coh.classOf X G ∈ (rankDegToK0 X).range := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro G hG
      by_cases hn : n = 0
      ·
        obtain ⟨m, hm⟩ := torsion_decomp G (by omega)
        rw [hm]; exact ⟨⟨0, m⟩, by simp [rankDegToK0]⟩
      ·
        obtain ⟨d, Q, hQ_rank, hQ_eq⟩ := rank_reduction G (by omega)
        rw [hQ_eq]
        have hQ_mem := ih (X.rank Q) (by omega) Q rfl
        obtain ⟨⟨r₃, d₃⟩, h₃⟩ := hQ_mem
        refine ⟨⟨1 + r₃, d + d₃⟩, ?_⟩
        simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₃ ⊢
        rw [← h₃]; module
  exact this (X.rank F) F rfl

end Lec24

namespace Lec24

/--
[K0_generators_lemma35](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma K0_generators_lemma35
  {X : SmoothCurveK0Data}
-- given
  (torsion_decomp : ∀ F : X.CohSheaf, X.rank F = 0 → ∃ (n : ℤ), K0Coh.classOf X F = n • K0Coh.classOf X X.O_x)
  (rank_reduction : ∀ F : X.CohSheaf, 0 < X.rank F → ∃ (d : ℤ) (Q : X.CohSheaf), X.rank Q < X.rank F ∧ K0Coh.classOf X F = K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x + K0Coh.classOf X Q) :
-- imply
  Function.Surjective (rankDegToK0 X) := by
-- proof
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z =>
    induction z using FreeAbelianGroup.induction_on with
    | zero => exact ⟨⟨0, 0⟩, by simp [rankDegToK0]⟩
    | of F => exact classOf_in_range X torsion_decomp rank_reduction F
    | neg F hF =>
      obtain ⟨⟨r, d⟩, hr⟩ := hF
      refine ⟨⟨-r, -d⟩, ?_⟩
      simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hr ⊢
      rw [QuotientAddGroup.mk_neg, neg_smul, neg_smul, ← neg_add, hr]
    | add x y hx hy =>
      obtain ⟨⟨r₁, d₁⟩, h₁⟩ := hx
      obtain ⟨⟨r₂, d₂⟩, h₂⟩ := hy
      refine ⟨⟨r₁ + r₂, d₁ + d₂⟩, ?_⟩
      simp only [rankDegToK0, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h₁ h₂ ⊢
      rw [QuotientAddGroup.mk_add, ← h₁, ← h₂, add_smul, add_smul]; abel

end Lec24

namespace Lec24

/--
[goal_185](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma goal_185
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  X.degK = 2 * (X.genus : ℤ) - 2 :=
-- proof
  X.deg_canonical_eq

end Lec24

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[pa_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma pa_eq_genus
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  X.arithmeticGenus_pa = (X.genus : ℤ) := by
-- proof
  unfold arithmeticGenus_pa
  rw [X.chi_structure]
  ring

end Lec24.SmoothCompleteCurveWithSheaves

namespace Lec24.SmoothCompleteCurveWithSheaves

/--
[pg_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
lemma pg_eq_genus
  {X : SmoothCompleteCurveWithSheaves} :
-- imply
  X.geometricGenus_pg = X.genus :=
-- proof
  X.arithmetic_eq_geometric_genus

end Lec24.SmoothCompleteCurveWithSheaves

/--
[euler_char_O_d_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec24RiemannRochSerre.lean)
-/
@[path]
private lemma euler_char_O_d_P1_eq
  {d : ℤ} :
-- imply
  (h0_P1 d : ℤ) - (h1_P1 d : ℤ) = d + 1 := by
-- proof
  apply Lec24.euler_char_O_d_P1 d


-- created on 2026-10-23
