import Mathlib
import Initialize.Tactic.Attr.Basic
open AlgebraicGeometry CategoryTheory


namespace Prop19

/--
[pushforward_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop19PushforwardEmbedding.lean)
-/
@[path]
lemma pushforward_characterization
  [CommRing R]
  {I : Ideal R}
  {M : Type*}
  [AddCommGroup M]
  [Module R M] :
-- imply
  I ≤ Module.annihilator R M ↔ ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
-- proof
  constructor
  · intro h r m hr
    exact (Module.mem_annihilator.mp (h hr)) m
  · intro h r hr
    exact Module.mem_annihilator.mpr (fun m => h r m hr)

end Prop19

namespace Prop19

/--
[pushforward_fullyFaithful](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop19PushforwardEmbedding.lean)
-/
@[path]
lemma pushforward_fullyFaithful
  {R : Type*}
  [CommRing R]
  {I : Ideal R} :
-- imply
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).Full ∧ (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).Faithful := by
-- proof
  refine ⟨?_, inferInstance⟩
  constructor
  intro M N g
  refine ⟨ModuleCat.ofHom ⟨g.hom.toAddHom, ?_⟩, ?_⟩
  ·
    intro s m
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact g.hom.map_smul r m
  · ext x; rfl

end Prop19

namespace Prop19

/--
[essential_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop19PushforwardEmbedding.lean)
-/
@[path]
lemma essential_image
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {M : ModuleCat R} :
-- imply
  (∃ (N : ModuleCat (R ⧸ I)), Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N ≅ M)) ↔ ∀ (r : R) (m : M), r ∈ I → r • m = 0 := by
-- proof
  constructor
  ·
    rintro ⟨N, ⟨iso⟩⟩ r m hr
    have key : r • (iso.inv.hom m) = (0 : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) := by
      change (Ideal.Quotient.mk I r) • (iso.inv.hom m : N) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
    have h1 := iso.hom.hom.map_smul r (iso.inv.hom m)
    rw [key, map_zero] at h1
    have h2 : iso.hom.hom (iso.inv.hom m) = m := by
      change (iso.inv ≫ iso.hom).hom m = m
      simp [iso.inv_hom_id]
    rw [h2] at h1; exact h1.symm
  ·
    intro hann
    have htors : Module.IsTorsionBySet R M (I : Set R) := by
      intro m ⟨a, ha⟩; exact hann a m ha
    letI := htors.module
    let N : ModuleCat (R ⧸ I) := ModuleCat.of (R ⧸ I) M
    refine ⟨N, ⟨?_⟩⟩
    exact { hom := ModuleCat.ofHom LinearMap.id, inv := ModuleCat.ofHom LinearMap.id,
      hom_inv_id := by ext; rfl, inv_hom_id := by ext; rfl }
section SchemeLevel
open AlgebraicGeometry CategoryTheory
universe u
/-- Proposition 19 (scheme version): for a closed immersion `i : Z → X`, the
pushforward `i_* : QCoh(Z) → QCoh(X)` is a fully faithful functor. -/
end SchemeLevel

end Prop19


-- created on 2026-10-23
