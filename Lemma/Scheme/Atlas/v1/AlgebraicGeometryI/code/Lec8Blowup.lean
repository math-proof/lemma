import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec8Blowup.Part2
open Lec8Blowup
open scoped LinearAlgebra.Projectivization


namespace Lec8Blowup

/--
[blowupEquations_iff_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
lemma blowupEquations_iff_mem_span
  [Field k]
  {n : ℕ}
  {x y : Fin n → k}
-- given
  (hy : y ≠ 0) :
-- imply
  BlowupEquations k n x y ↔ x ∈ Submodule.span k {y} := by
-- proof
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    have ⟨j, hyj⟩ : ∃ j : Fin n, y j ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hy (funext hall)
    refine ⟨x j * (y j)⁻¹, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    have heq := h i j
    calc x j * (y j)⁻¹ * y i = x j * y i * (y j)⁻¹ := by ring
      _ = x i * y j * (y j)⁻¹ := by rw [heq]
      _ = x i := by field_simp
  · rintro ⟨a, rfl⟩ i j
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end Lec8Blowup

namespace Lec8Blowup

/--
[mem_blowupAffineOrigin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
lemma mem_blowupAffineOrigin_iff
  [Field k]
  {n : ℕ}
  {k : Type*}
  [Field k]
  {n : ℕ}
  {p : (Fin n → k) × ℙ k (Fin n → k)} :
-- imply
  p ∈ BlowupAffineOrigin k n ↔ BlowupEquations k n p.1 p.2.rep := by
-- proof
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq,
    Projectivization.submodule_eq_span_rep]
  exact (blowupEquations_iff_mem_span p.2.rep_nonzero).symm

end Lec8Blowup

namespace Lec8Blowup

/--
[nonzero_mem_blowupAffineOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
lemma nonzero_mem_blowupAffineOrigin
  [Field k]
  {n : ℕ}
  {x : Fin n → k}
-- given
  (hx : x ≠ 0) :
-- imply
  (x, Projectivization.mk k x hx) ∈ BlowupAffineOrigin k n := by
-- proof
  simp only [BlowupAffineOrigin, Set.mem_setOf_eq, Projectivization.submodule_mk]
  exact Submodule.mem_span_singleton_self x

end Lec8Blowup

/--
[Projectivization.submodule_eq_span_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
private lemma submodule_eq_span_rep_eq
  [Field k]
  {n : ℕ}
  {v : ℙ k (Fin n → k)} :
-- imply
  v.submodule = k ∙ v.rep := by
-- proof
  apply Lec8Blowup.Projectivization.submodule_eq_span_rep v

/--
[proj_unique_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
private lemma proj_unique_of_nonzero_eq
  [Field k]
  {n : ℕ}
  {x : Fin n → k}
  {l : ℙ k (Fin n → k)}
-- given
  (hx : x ≠ 0)
  (hmem : x ∈ l.submodule) :
-- imply
  l = Projectivization.mk k x hx := by
-- proof
  apply Lec8Blowup.proj_unique_of_nonzero hx l hmem

/--
[zero_mem_blowupAffineOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8Blowup.lean)
-/
@[path]
private lemma zero_mem_blowupAffineOrigin_eq
  [Field k]
  {n : ℕ}
  {l : ℙ k (Fin n → k)} :
-- imply
  ((0 : Fin n → k), l) ∈ BlowupAffineOrigin k n := by
-- proof
  apply Lec8Blowup.zero_mem_blowupAffineOrigin l


-- created on 2026-10-23
