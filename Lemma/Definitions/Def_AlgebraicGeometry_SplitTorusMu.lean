import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.SplitTorus

abbrev muCoord (S : Type u) [CommRing S] (t m : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ZMod m)

abbrev muScheme (S : Type u) [CommRing S] (t m : ℕ) : Scheme.{u} := Spec (CommRingCat.of (muCoord S t m))

abbrev muStr (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (muCoord S t m)))

abbrev torusCoord (S : Type u) [CommRing S] (t : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ℤ)

abbrev torusScheme (S : Type u) [CommRing S] (t : ℕ) : Scheme.{u} := Spec (CommRingCat.of (torusCoord S t))

abbrev torusStr (S : Type u) [CommRing S] (t : ℕ) : torusScheme S t ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)))

abbrev muToTorus (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))

abbrev muIncl (S : Type u) [CommRing S] (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muScheme S t m ⟶ muScheme S t m' :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i))))

abbrev muBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t m : ℕ) :
    muScheme S' t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) φ))

abbrev torusBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t : ℕ) :
    torusScheme S' t ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) φ))

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
