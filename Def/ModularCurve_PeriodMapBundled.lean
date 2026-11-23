module

public import Theorem.UpperHalfPlane.PeriodMap
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups

def HasEquivariantPrimitive (N : ℕ) (f : CuspForm (Gamma0 N) 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    IsEquivariantPrimitive (Gamma0 N) F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

noncomputable def periodMap (N : ℕ) (f : CuspForm (Gamma0 N) 2) : Additive (Gamma0 N) →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F then h.choose_spec.2.2.1.periodHom else 0

end ModularCurve
