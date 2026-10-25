import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Abbrev.AlgebraicGeometry_SplitTorusMu

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.SplitTorus


def muPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t m : ℕ) (χ : muCoord S t m →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

def torusPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t : ℕ) (χ : torusCoord S t →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

def torusPtId (S : Type u) [CommRing S] (t : ℕ) (χ : torusCoord S t →ₐ[S] S) : SchemeHomOver (𝟙 _) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

def muPtId (S : Type u) [CommRing S] (t m : ℕ) (χ : muCoord S t m →ₐ[S] S) : SchemeHomOver (𝟙 _) (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (muCoord S t m)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

end AlgebraicGeometry.SplitTorus

end
