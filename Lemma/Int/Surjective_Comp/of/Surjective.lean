import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.TensorHomAxiom
open scoped TensorProduct


/--
[postcomp_surjective_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TensorHomAxiom.lean)
-/
@[path]
private lemma postcomp_surjective_of_free
  {R : Type u}
  [CommRing R]
  {V : Type u}
  [AddCommGroup V]
  [Module R V]
  [Module.Free R V]
  {X : Type u}
  [AddCommGroup X]
  [Module R X]
  {Y : Type u}
  [AddCommGroup Y]
  [Module R Y]
  {f : X →ₗ[R] Y}
-- given
  (hf : Function.Surjective f) :
-- imply
  Function.Surjective (fun (φ : V →ₗ[R] X) => f.comp φ) := by
-- proof
  intro ψ
  have : Module.Projective R V := Module.Projective.of_free
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f ψ hf
  exact ⟨φ, by ext v; exact LinearMap.congr_fun hφ v⟩


-- created on 2026-10-23
-- updated on 2026-10-24
