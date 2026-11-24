module
public import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part5
public import Theorem.Nat.NumberField.RayClass.Modulus
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic
public import Def.NumberTheory.NumberField.RayClass.RayGroup.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayGroup.lean -/
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray groups attached to a modulus (N403 foundation)

Built over `NumberField.Modulus`, whose infinite-place multiplication
uses union, representing truncated exponent addition `min (m v + n v) 1`
(the ATLAS-extracted `max` formula was a typo).
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

theorem rayGenerators_mem_of_isRayElementOne (m : Modulus K) (x : Kˣ)
    (hx : IsRayElementOne m x) :
    (⟨toPrincipalIdeal (𝓞 K) K x,
      Subgroup.mem_comap.mp hx.1⟩ :
      coprimeFractionalIdeals m) ∈ rayGenerators m :=
  ⟨x, hx, rfl⟩

theorem mem_rayGroup_of_isRayElementOne (m : Modulus K) (x : Kˣ)
    (hx : IsRayElementOne m x) :
    (⟨toPrincipalIdeal (𝓞 K) K x,
      Subgroup.mem_comap.mp hx.1⟩ :
      coprimeFractionalIdeals m) ∈ rayGroup m :=
  Subgroup.subset_closure (rayGenerators_mem_of_isRayElementOne m x hx)

theorem rayGroup_closure_le {m : Modulus K}
    {H : Subgroup (coprimeFractionalIdeals m)}
    (h : rayGenerators m ⊆ (↑H : Set _)) : rayGroup m ≤ H :=
  (Subgroup.closure_le H).2 h

theorem congruentOneAtFinitePart_one (m : Modulus K) :
    CongruentOneAtFinitePart m 1 := fun _ _ => Or.inl rfl

end Modulus
end NumberField
