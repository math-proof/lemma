import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits Opposite

/--
[CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural.lean)
-/
@[path]
private lemma main
  {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  {F G : Sheaf J Ab.{w}}
-- given
  (e : ∀ U : Cᵒᵖ, F.obj.obj U ≃+ G.obj.obj U)
  (he : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (s : F.obj.obj U), e V (F.obj.map k s) = G.obj.map k (e U s)) :
-- imply
  ∃ φ : F ≅ G, ∀ (U : Cᵒᵖ) (s : F.obj.obj U), φ.hom.hom.app U s = e U s := by
-- proof
  let α : F.obj ≅ G.obj := NatIso.ofComponents (fun U => (e U).toAddCommGrpIso) (by
    intro U V k
    ext s
    simpa using he k s)
  refine ⟨(sheafToPresheaf J Ab.{w}).preimageIso α, fun U s => ?_⟩
  have : ((sheafToPresheaf J Ab.{w}).preimageIso α).hom.hom = α.hom := by
    have h := (sheafToPresheaf J Ab.{w}).map_preimage α.hom
    simpa using h
  rw [this]
  rfl


-- created on 2026-10-05
