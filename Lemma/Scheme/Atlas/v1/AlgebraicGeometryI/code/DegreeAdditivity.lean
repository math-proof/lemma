import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DegreeAdditivity
open Submodule DegreeAdditivity


namespace DegreeAdditivity

/--
[length_eq_torsionDegree_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma length_eq_torsionDegree_add
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  Module.length R M = torsionDegree R M + Module.length R (M ⧸ torsion R M) :=
-- proof
  Module.length_eq_add_of_exact
    (torsion R M).subtype (torsion R M).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)

end DegreeAdditivity

namespace DegreeAdditivity

/--
[torsionDegree_of_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma torsionDegree_of_torsion
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
-- given
  (htor : Module.IsTorsion R M) :
-- imply
  torsionDegree R M = Module.length R M := by
-- proof
  unfold torsionDegree
  have h : torsion R M = ⊤ := by
    ext x; simp only [mem_top, iff_true]
    exact (mem_torsion_iff x).mpr (@htor x)
  rw [h, Module.length_top]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[torsionDegree_of_torsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma torsionDegree_of_torsionFree
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
-- given
  (htf : Module.IsTorsionFree R M) :
-- imply
  torsionDegree R M = 0 := by
-- proof
  unfold torsionDegree
  rw [isTorsionFree_iff_torsion_eq_bot.mp htf, Module.length_bot]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[torsionDegree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma torsionDegree_zero
  {R : Type*}
  [CommRing R]
  [IsDomain R] :
-- imply
  torsionDegree R PUnit = 0 := by
-- proof
  unfold torsionDegree
  exact Module.length_eq_zero

end DegreeAdditivity

namespace DegreeAdditivity

/--
[LinearMap.map_torsion_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma LinearMap.map_torsion_mem
  [CommRing R]
  [IsDomain R]
  [AddCommGroup N]
  [Module R N]
  [AddCommGroup M]
  [Module R M]
  {f : N →ₗ[R] M}
  {x : N}
-- given
  (hx : x ∈ torsion R N) :
-- imply
  f x ∈ torsion R M := by
-- proof
  rw [mem_torsion_iff] at hx ⊢
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  refine ⟨⟨a, ha⟩, ?_⟩
  show (a : R) • f x = 0
  rw [← f.map_smul]
  have : (a : R) • x = (0 : N) := hax
  rw [this, map_zero]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[lemma34_ses_length_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma lemma34_ses_length_additive
  [Ring R]
  [AddCommGroup N]
  [AddCommGroup M]
  [AddCommGroup P]
  [Module R N]
  [Module R M]
  [Module R P]
  {f : N →ₗ[R] M}
  {g : M →ₗ[R] P}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hex : Function.Exact f g) :
-- imply
  Module.length R M = Module.length R N + Module.length R P :=
-- proof
  Module.length_eq_add_of_exact f g hf hg hex

end DegreeAdditivity

namespace DegreeAdditivity

/--
[lemma34_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma lemma34_submodule
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
-- proof
  Module.length_eq_add_of_exact N.subtype N.mkQ
    (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
    (LinearMap.exact_subtype_mkQ N)

end DegreeAdditivity

namespace DegreeAdditivity

/--
[length_le_of_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma length_le_of_submodule
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  Module.length R N ≤ Module.length R M := by
-- proof
  rwa [lemma34_submodule N]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[dvr_ord_uniformizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma dvr_ord_uniformizer
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {π : R}
-- given
  (hπ : Irreducible π) :
-- imply
  Ring.ord R π = 1 := by
-- proof
  unfold Ring.ord
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  exact ⟨Ideal.span {π},
    by rw [← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R,
    ⟨LinearEquiv.refl R _⟩⟩

end DegreeAdditivity

namespace DegreeAdditivity

/--
[dvr_ord_uniformizer_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma dvr_ord_uniformizer_pow
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {π : R}
  {n : ℕ}
-- given
  (hπ : Irreducible π) :
-- imply
  Ring.ord R (π ^ n) = n := by
-- proof
  induction n with
  | zero => simp [Ring.ord]
  | succ k ih =>
    have hπ_nzd : π ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero
    rw [pow_succ, Ring.ord_mul R hπ_nzd, ih, dvr_ord_uniformizer R hπ]
    simp [Nat.cast_succ]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[dvr_determinant_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma dvr_determinant_length
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  {a b : R}
-- given
  (hb : b ∈ nonZeroDivisors R) :
-- imply
  Ring.ord R (a * b) = Ring.ord R a + Ring.ord R b :=
-- proof
  Ring.ord_mul R hb

end DegreeAdditivity

namespace DegreeAdditivity

/--
[top_exterior_power_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma top_exterior_power_rank_one
  {R : Type*}
  [CommRing R]
  [Nontrivial R]
  [StrongRankCondition R]
  {n : ℕ} :
-- imply
  Module.finrank R (⋀[R]^n (Fin n → R)) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_self, Nat.choose_self]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[exterior_power_vanishes_above_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma exterior_power_vanishes_above_rank
  {R : Type*}
  [CommRing R]
  [Nontrivial R]
  [StrongRankCondition R]
  {n p : ℕ}
-- given
  (hp : n < p) :
-- imply
  Module.finrank R (⋀[R]^p (Fin n → R)) = 0 := by
-- proof
  rw [exteriorPower.finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_self, Nat.choose_eq_zero_of_lt hp]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_respects_K0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_respects_K0
  [Ring R]
  {rel : K0SESRelation R} :
-- imply
  Module.length R rel.M = Module.length R rel.N + Module.length R rel.P :=
-- proof
  Module.length_eq_add_of_exact rel.f rel.g rel.f_inj rel.g_surj rel.exact

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_respects_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_respects_iso
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {e : M ≃ₗ[R] N} :
-- imply
  Module.length R M = Module.length R N :=
-- proof
  e.length_eq

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_additive_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_additive_prod
  {R : Type*}
  [Ring R]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N] :
-- imply
  Module.length R (M × N) = Module.length R M + Module.length R N :=
-- proof
  Module.length_prod R M N

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_zero
  {R : Type*}
  [Ring R] :
-- imply
  Module.length R PUnit = 0 := by
-- proof
  haveI : Subsingleton PUnit := inferInstance
  exact Module.length_eq_zero

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_simple
  {R : Type*}
  [Ring R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [IsSimpleModule R M] :
-- imply
  Module.length R M = 1 :=
-- proof
  Module.length_eq_one R M

end DegreeAdditivity

namespace DegreeAdditivity

/--
[degree_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma degree_finite
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [IsArtinian R M]
  [IsNoetherian R M] :
-- imply
  Module.length R M ≠ ⊤ :=
-- proof
  Module.length_ne_top

end DegreeAdditivity

namespace DegreeAdditivity

/--
[dedekind_localization_is_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma dedekind_localization_is_dvr
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {P : Ideal R}
  [P.IsPrime]
-- given
  (hP : P ≠ ⊥) :
-- imply
  IsDiscreteValuationRing (Localization.AtPrime P) :=
-- proof
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _

end DegreeAdditivity

namespace DegreeAdditivity

/--
[dvr_torsionFree_is_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean)
-/
@[path]
lemma dvr_torsionFree_is_free
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [Module.IsTorsionFree R M] :
-- imply
  Module.Free R M :=
-- proof
  inferInstance
end DegreeAdditivity



-- created on 2026-10-23
