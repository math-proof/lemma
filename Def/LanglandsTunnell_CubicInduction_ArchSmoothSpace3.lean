module

public import Def.LanglandsTunnell_CubicInduction_ArchCentre3

@[expose] public section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

private def invertibleEntries : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private def unipotentEntries (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private def oneEntries : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private def elementaryEntries (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

private def realAdeleHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

def smoothFunctions3 : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := {φ | WhittakerBlock.IsArchSmooth3 φ}
  zero_mem' := by
    intro g
    exact contDiffOn_const
  add_mem' := by
    intro φ ψ hφ hψ g
    exact (hφ g).add (hψ g)
  smul_mem' := by
    intro c φ hφ g
    exact (hφ g).const_smul c

def archDerivₗ (i j : Fin 3) : smoothFunctions3 →ₗ[ℂ] smoothFunctions3 where
  toFun φ := ⟨archDeriv i j φ, isArchSmooth3_archDeriv φ.2 i j⟩
  map_add' φ ψ := Subtype.ext <| funext fun g =>
    ((differentiableAt_unipotent φ.2 i j g).hasDerivAt.add (differentiableAt_unipotent ψ.2 i j g).hasDerivAt).deriv
  map_smul' c φ := Subtype.ext <| funext fun g =>
    ((differentiableAt_unipotent φ.2 i j g).hasDerivAt.const_smul c).deriv

end LanglandsTunnell.CubicInduction.WhittakerBlock

end

end
