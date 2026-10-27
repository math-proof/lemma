import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafTensorExact
open SheafTensorExact


namespace SheafTensorExact

/--
[locally_free_isFlat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean)
-/
@[path]
lemma locally_free_isFlat
  {R : Type*}
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  {n : ℕ}
-- given
  (hlf : IsLocallyFree R M n) :
-- imply
  Module.Flat R M := by
-- proof
  obtain ⟨S, hspan, hfree⟩ := hlf
  apply Module.flat_of_localized_span R M (S : Set R) hspan
  intro ⟨f, hf⟩
  have hfr := (hfree f hf).1
  haveI : Module.Free (Localization.Away f) (LocalizedModule.Away f M) := hfr
  haveI : Module.Flat (Localization.Away f) (LocalizedModule.Away f M) := inferInstance
  haveI : Module.Flat R (Localization.Away f) :=
    IsLocalization.flat (Localization.Away f) (Submonoid.powers f)
  exact Module.Flat.trans R (Localization.Away f) (LocalizedModule.Away f M)

end SheafTensorExact

namespace SheafTensorExact

/--
[locally_free_tensor_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean)
-/
@[path]
lemma locally_free_tensor_exact
  {R : Type*}
  [CommRing R]
  {L : Type*}
  [AddCommGroup L]
  [Module R L]
  {n : ℕ}
  [AddCommGroup F']
  [Module R F']
  [AddCommGroup F]
  [Module R F]
  [AddCommGroup F'']
  [Module R F'']
  {f : F' →ₗ[R] F}
  {g : F →ₗ[R] F''}
-- given
  (hlf : IsLocallyFree R L n)
  (hex : Function.Exact f g) :
-- imply
  Function.Exact (f.rTensor L) (g.rTensor L) := by
-- proof
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact Module.Flat.rTensor_exact L hex

end SheafTensorExact

namespace SheafTensorExact

/--
[locally_free_tensor_short_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean)
-/
@[path]
lemma locally_free_tensor_short_exact
  {R : Type*}
  [CommRing R]
  {L : Type*}
  [AddCommGroup L]
  [Module R L]
  {n : ℕ}
  [AddCommGroup F']
  [Module R F']
  [AddCommGroup F]
  [Module R F]
  [AddCommGroup F'']
  [Module R F'']
  {f : F' →ₗ[R] F}
  {g : F →ₗ[R] F''}
-- given
  (hlf : IsLocallyFree R L n)
  (hinj : Function.Injective f)
  (hex : Function.Exact f g)
  (hsurj : Function.Surjective g) :
-- imply
  Function.Injective (f.rTensor L) ∧ Function.Exact (f.rTensor L) (g.rTensor L) ∧ Function.Surjective (g.rTensor L) := by
-- proof
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact ⟨Module.Flat.rTensor_preserves_injective_linearMap f hinj,
    Module.Flat.rTensor_exact L hex,
    LinearMap.rTensor_surjective L hsurj⟩

end SheafTensorExact

namespace SheafTensorExact

/--
[locally_free_lTensor_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean)
-/
@[path]
lemma locally_free_lTensor_exact
  {R : Type*}
  [CommRing R]
  {L : Type*}
  [AddCommGroup L]
  [Module R L]
  {n : ℕ}
  [AddCommGroup F']
  [Module R F']
  [AddCommGroup F]
  [Module R F]
  [AddCommGroup F'']
  [Module R F'']
  {f : F' →ₗ[R] F}
  {g : F →ₗ[R] F''}
-- given
  (hlf : IsLocallyFree R L n)
  (hex : Function.Exact f g) :
-- imply
  Function.Exact (f.lTensor L) (g.lTensor L) := by
-- proof
  haveI : Module.Flat R L := locally_free_isFlat R L n hlf
  exact Module.Flat.lTensor_exact L hex

end SheafTensorExact

namespace SheafTensorExact

/--
[invertible_sheaf_tensor_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafTensorExact.lean)
-/
@[path]
lemma invertible_sheaf_tensor_exact
  {R : Type*}
  [CommRing R]
  {L : Type*}
  [AddCommGroup L]
  [Module R L]
  [AddCommGroup F']
  [Module R F']
  [AddCommGroup F]
  [Module R F]
  [AddCommGroup F'']
  [Module R F'']
  {f : F' →ₗ[R] F}
  {g : F →ₗ[R] F''}
-- given
  (hlf : IsLocallyFree R L 1)
  (hex : Function.Exact f g) :
-- imply
  Function.Exact (f.rTensor L) (g.rTensor L) :=
-- proof
  locally_free_tensor_exact R L 1 hlf f g hex

end SheafTensorExact


-- created on 2026-10-23
