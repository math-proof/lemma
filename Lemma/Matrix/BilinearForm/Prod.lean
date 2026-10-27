import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.LinearAlgebra.BilinearForm.Prod
open LinearMap (BilinForm)
open Module
open LinearMap
open BilinForm


namespace LinearMap.BilinForm

/--
[nondegenerate_prod_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
lemma nondegenerate_prod_iff
  [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂} :
-- imply
  (B₁.prod B₂).Nondegenerate ↔ B₁.Nondegenerate ∧ B₂.Nondegenerate := by
-- proof
  have sepL : (B₁.prod B₂).SeparatingLeft ↔
    B₁.SeparatingLeft ∧ B₂.SeparatingLeft := by
    constructor
    · intro h
      refine ⟨fun x₁ hx₁ => ?_, fun x₂ hx₂ => ?_⟩
      · have hmem : (x₁, 0) = (0 : M₁ × M₂) :=
        h _ fun y => by simpa using hx₁ y.1
        exact congrArg Prod.fst hmem
      · have hmem : ((0 : M₁), x₂) = (0 : M₁ × M₂) :=
        h _ fun y => by simpa using hx₂ y.2
        exact congrArg Prod.snd hmem
    · rintro ⟨h₁, h₂⟩ x hx
      have e₁ : x.1 = 0 := h₁ _ fun y₁ => by simpa using hx (y₁, 0)
      have e₂ : x.2 = 0 := h₂ _ fun y₂ => by simpa using hx (0, y₂)
      exact Prod.ext e₁ e₂
  have sepR : (B₁.prod B₂).SeparatingRight ↔
    B₁.SeparatingRight ∧ B₂.SeparatingRight := by
    constructor
    · intro h
      refine ⟨fun y₁ hy₁ => ?_, fun y₂ hy₂ => ?_⟩
      · have hmem : (y₁, 0) = (0 : M₁ × M₂) :=
        h _ fun x => by simpa using hy₁ x.1
        exact congrArg Prod.fst hmem
      · have hmem : ((0 : M₁), y₂) = (0 : M₁ × M₂) :=
        h _ fun x => by simpa using hy₂ x.2
        exact congrArg Prod.snd hmem
    · rintro ⟨h₁, h₂⟩ y hy
      have e₁ : y.1 = 0 := h₁ _ fun x₁ => by simpa using hy (x₁, 0)
      have e₂ : y.2 = 0 := h₂ _ fun x₂ => by simpa using hy (0, x₂)
      exact Prod.ext e₁ e₂
  constructor
  · rintro ⟨hL, hR⟩
    exact ⟨⟨(sepL.mp hL).1, (sepR.mp hR).1⟩,
      ⟨(sepL.mp hL).2, (sepR.mp hR).2⟩⟩
  · rintro ⟨⟨h1L, h1R⟩, ⟨h2L, h2R⟩⟩
    exact ⟨sepL.mpr ⟨h1L, h2L⟩, sepR.mpr ⟨h1R, h2R⟩⟩
section PerfPair
variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂]

end LinearMap.BilinForm

namespace LinearMap.BilinForm

/--
[dualSubmodule_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
lemma dualSubmodule_prod
  [CommRing R] [Field S] [AddCommGroup M₁] [AddCommGroup M₂] [Algebra R S] [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂] [IsScalarTower R S M₁] [IsScalarTower R S M₂]
  {B₁ : BilinForm S M₁}
  {B₂ : BilinForm S M₂}
  {N₁ : Submodule R M₁}
  {N₂ : Submodule R M₂} :
-- imply
  (B₁.prod B₂).dualSubmodule (N₁.prod N₂) =
    (B₁.dualSubmodule N₁).prod (B₂.dualSubmodule N₂) := by
-- proof
  ext x
  simp only [mem_dualSubmodule, Submodule.mem_prod]
  constructor
  · rintro h
    refine ⟨fun y₁ hy₁ => ?_, fun y₂ hy₂ => ?_⟩
    · have h0 := h (y₁, 0) ⟨hy₁, Submodule.zero_mem _⟩
      simpa using h0
    · have h0 := h (0, y₂) ⟨Submodule.zero_mem _, hy₂⟩
      simpa using h0
  · rintro ⟨h₁, h₂⟩ y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    simpa [prod_apply] using add_mem (h₁ _ hy₁) (h₂ _ hy₂)

end LinearMap.BilinForm

/--
[prod_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/Prod.lean)
-/
@[path]
private lemma prod_apply_eq
  [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂}
  {x y : M₁ × M₂} :
-- imply
  B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 := by
-- proof
  apply LinearMap.BilinForm.prod_apply B₁ B₂ x y


-- created on 2026-10-20
-- updated on 2026-10-26
