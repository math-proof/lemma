import Mathlib
import sympy.Basic
open CategoryTheory Limits MonoidalCategory


namespace SingularCohomology

/--
[exact_kernel_ι_ModuleCat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CupProductHelpers.lean)
-/
@[path]
28 helper for the cup product).  For any morphism `f : A ⟶ B` in
`ModuleCat R`, the underlying linear-map sequence
`kernel.ι f → f` is exact in the sense of `Function.Exact`: the image of
`kernel.ι f` coincides with the kernel of `f`.  This bridges Mathlib's
categorical `kernel.ι` with the concrete linear-algebra notion of
exactness used in the cohomology development. -/
lemma exact_kernel_ι_ModuleCat {R : Type} [CommRing R] {A B : ModuleCat.{0} R}
  (f : A ⟶ B) : Function.Exact (kernel.ι f).hom f.hom := by
  rw [LinearMap.exact_iff]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    rw [← ModuleCat.kernelIsoKer_hom_ker_subtype f]
    simp only [ModuleCat.hom_comp]
    exact ⟨(ModuleCat.kernelIsoKer f).inv.hom ⟨x, hx⟩, by simp⟩
  · rintro ⟨y, rfl⟩
    change (kernel.ι f ≫ f).hom y = (0 : kernel f ⟶ B).hom y
    rw [kernel.condition]

end SingularCohomology

/--
[exact_kernel_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CupProductHelpers.lean)
-/
@[path]
private lemma exact_kernel__eq
  {R : Type}
  [CommRing R]
  {A B : ModuleCat.{0} R}
  {f : A ⟶ B} :
-- imply
  Function.Exact (kernel.ι f).hom f.hom := by
-- proof
  apply SingularCohomology.exact_kernel_ f


-- created on 2026-10-23
