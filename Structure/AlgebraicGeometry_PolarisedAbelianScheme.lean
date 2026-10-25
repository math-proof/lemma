import Mathlib.Topology.KrullDimension
import Structure.JacJ1Iface
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

def finComb {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) : SchemeHomOver t f :=
  letI := L.pointGroup t
  (List.ofFn fun i => x i ^ c i).prod

end GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicGeometry

def Scheme.Modules.geomFibreH0Finrank {S : Type u} [CommRing S] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (M : A.Modules) (k : Type u) [Field k] (sk : S →+* k) : ℕ :=
  letI : Algebra k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤) :=
    Module.compHom _ (algebraMap k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
  Module.finrank k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤)

structure PolarisedAbelianScheme (g d n : ℕ) (S : Type u) [CommRing S] : Type (u + 1) where

  A : Scheme.{u}

  f : A ⟶ Spec (CommRingCat.of S)

  L : RelativeGroupLaw S f

  comm : L.IsCommutative

  bundle : AbelianSchemePropertyBundle S f

  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g

  P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f

  P_torsion : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))

  P_indep : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * g) → Fin n),
    L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
      L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
      c = c'

  P_span : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f),
    L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
      ∃ c : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q

  pol : A.Modules

  pol_isInvertible : Scheme.Modules.IsInvertible pol

  pol_veryAmple : Scheme.Modules.ClosedImmersionBySections pol f

  pol_finrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank f pol k sk = d

namespace PolarisedAbelianScheme

variable {g d n : ℕ}


def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S') : Prop :=
  ∃ (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (u'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol)

structure IsFineModuli (g d n : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      PolarisedAbelianScheme g d n S → SchemeHomOver s πM) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), Iso u u' → pt S s u = pt S s u'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
    IsPullback φ u u' → (pt S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s u).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ u : PolarisedAbelianScheme g d n S, pt S s u = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), pt S s u = pt S s u' → Iso u u'

end PolarisedAbelianScheme

end AlgebraicGeometry

end
