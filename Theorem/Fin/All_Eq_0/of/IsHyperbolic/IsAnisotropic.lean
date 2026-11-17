module

public import Mathlib
public import Theorem.Int.OrthogonalSum.eq.Add
public import Theorem.Fin.Any_And_Eq_0AndEq_1.of.Eq_0.Ne_0.IsSymm.Nondegenerate

public section


/--
[anisotropic_hyperbolic_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/AnisotropicHyperbolicTrivial.lean)
-/
public theorem Fin.All_Eq_0.of.IsHyperbolic.IsAnisotropic
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hAniso : BilinForm.IsAnisotropic B)
  (hHyp : BilinForm.IsHyperbolic B) :
-- imply
  ∀ v : V, v = 0 := by
-- proof
  obtain ⟨W, hW_iso, hW_orth, _hnd⟩ := hHyp
  have hW_bot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    exact hAniso w (hW_iso w hw w hw)
  rw [hW_bot] at hW_orth
  intro v
  have hv_in_orth : v ∈ LinearMap.BilinForm.orthogonal B ⊥ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    unfold LinearMap.BilinForm.IsOrtho
    rw [(Submodule.mem_bot k).mp hw]
    simp [map_zero]
  rw [hW_orth] at hv_in_orth
  exact (Submodule.mem_bot k).mp hv_in_orth



-- created on 2026-10-23
-- updated on 2026-10-24
