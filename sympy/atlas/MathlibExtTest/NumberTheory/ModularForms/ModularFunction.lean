/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ModularForms/ModularFunction.lean -/

import sympy.atlas.NumberTheory.ModularForms.ModularFunction
/-! # Tests for modular functions -/
open scoped UpperHalfPlane MatrixGroups
variable {f : ℍ → ℂ} {Gamma : Subgroup SL(2, ℤ)}
example (c : ℂ) : ModularFunction.IsMeromorphicOnH (fun _ : ℍ => c) :=
  ⟨fun _ : ℂ => c, fun z _ => MeromorphicAt.const c z, fun _ => rfl⟩
example (c : ℂ) : ModularFunction.IsInvariantUnder (fun _ : ℍ => c) Gamma := by
  intro gamma hgamma tau
  rfl
example (hmero : ModularFunction.IsMeromorphicOnH f)
    (hinv : ModularFunction.IsInvariantUnder f Gamma)
    (hcusps : ModularFunction.IsMeromorphicAtCusps f) :
    IsModularFunction f Gamma :=
  ⟨hmero, hinv, hcusps⟩

example (hf : IsModularFunction f Gamma) : ModularFunction.IsMeromorphicOnH f :=
  hf.meromorphicOnH

example (hf : IsModularFunction f Gamma) : ModularFunction.IsInvariantUnder f Gamma :=
  hf.invariant

example (hf : IsModularFunction f Gamma) : ModularFunction.IsMeromorphicAtCusps f :=
  hf.meromorphicAtCusps

example (c : ℂ) (Gamma : Subgroup SL(2, ℤ)) :
    IsModularFunction (fun _ : ℍ => c) Gamma where
  meromorphicOnH :=
    ⟨fun _ : ℂ => c, fun z _ => MeromorphicAt.const c z, fun _ => rfl⟩
  invariant := by
    intro gamma hgamma tau
    rfl
  meromorphicAtCusps := fun gamma =>
    ⟨1, Nat.one_pos, fun _ => c, MeromorphicAt.const c 0,
      Filter.Eventually.of_forall fun _ => rfl⟩

example {f : UpperHalfPlane → ℂ} {Gamma H : Subgroup SL(2, ℤ)}
    (hf : IsModularFunction f Gamma) (h : H ≤ Gamma) :
    IsModularFunction f H where
  meromorphicOnH := hf.meromorphicOnH
  invariant := by
    intro gamma hgamma tau
    exact hf.invariant gamma (h hgamma) tau
  meromorphicAtCusps := hf.meromorphicAtCusps
