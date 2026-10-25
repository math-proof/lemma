import Mathlib
import Structure.ModularCurve_JZeroNeronObjectAtP
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Def.AlgebraicGeometry_NeronSpecialFibreRestriction
import Instance.ModularCurve_XHDifferentialsModL
import Def.ModularCurve_XHOperators
import Lemma.AlgebraicCurve.GluedPic0
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification
import Instance.ModularCurve_JHNeronObjectAtP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing
open ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace JHNeronObjectAtP


abbrev Fbar (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (κ : Type) [Field κ] : Type :=
  ↥(qExpFunctionFieldC κ (ΓN p M H hpM))

structure LevelData (p M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) where

  σA : Spec (CommRingCat.of ↥A) ⟶ base p

  hσA : barPt A ≫ σA = genPt p

  X : Scheme.{0}

  f : X ⟶ base p

  L : RelativeGroupLaw (baseRing p) f

  pts : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) f

  ptsSp : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ SchemeHomOver (resPt A ≫ σA) f

end JHNeronObjectAtP

open JHNeronObjectAtP in

structure JHNeronObjectAtP (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) where

  G : Scheme.{0}

  g : G ⟶ base p

  L : RelativeGroupLaw (baseRing p) g

  pts : JH M H ≃ SchemeHomOver (genPt p) g

  comm : L.IsCommutative

  smooth : Smooth g
  separated : IsSeparated g
  locallyOfFiniteType : LocallyOfFiniteType g
  quasiCompact : QuasiCompact g
  surjective : Surjective g
  fibre_preconnected : ∀ s : base p, _root_.IsPreconnected (g.base ⁻¹' {s})

  pts_add : ∀ x y : JH M H, pts (x + y) = L.mul _ (pts x) (pts y)

  pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
    (pts (σ • x)).1 =
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1

  hecke : ∀ (S : Set ℕ), CohCarrier.Gen M S → SchemeHomOver g g

  hecke_mul : ∀ (S : Set ℕ) (t : CohCarrier.Gen M S) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) (hecke S t) =
      L.mul s (NeronModelInfra.schemeHomOverComp x (hecke S t)) (NeronModelInfra.schemeHomOverComp y (hecke S t))

  hecke_pts : ∀ (S : Set ℕ) (t : CohCarrier.Gen M S) (x : JH M H),
    (pts (genOpH M H S t x)).1 = (pts x).1 ≫ (hecke S t).1

  nsmul_flat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n)
  nsmul_surjective : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n)

  proper_generic : IsProper (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))))

  toricRank : ℕ

  torusFibre : SchemeHomOver (torusStr (ResidueField ↥A) toricRank)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)

  torusFibre_isClosedImmersion : IsClosedImmersion torusFibre.1

  torusFibre_mul :
    ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) torusFibre =
        (L.baseChange (resPt A ≫ Λ.σA)).mul _
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) torusFibre)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) torusFibre)

  abqFibre : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)
  abqFibre_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ Λ.σA)).mul s x y) (abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).mul s (NeronModelInfra.schemeHomOverComp x (abqFibre i))
          (NeronModelInfra.schemeHomOverComp y (abqFibre i))
  abqFibre_flat : Flat (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm))
  abqFibre_surjective :
    Surjective (pullback.lift (abqFibre 0).1 (abqFibre 1).1 ((abqFibre 0).2.trans (abqFibre 1).2.symm))

  abqFibre_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) g)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abqFibre i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = x

  abqFibre_twist : ∀ (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA)) (i : Fin 2)
      (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      fibreMap (abqFibre i) (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 x) =
        GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (fibreMap (abqFibre i) x)

  ssFinset : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
    Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))

  mem_ssFinset_iff : ∀ s, s ∈ ssFinset ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p

  toricRank_succ_eq_card : toricRank + 1 = ssFinset.card

  ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ssFinset ≃
    SchemeHomOver (resPt A ≫ Λ.σA) g

  ptsSp_add : ∀ x y, ptsSp (x + y) =
      ofFibrePt ((L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y)))

  abqFibre_ptsSp : ∀ (x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ssFinset) (i : Fin 2),
      Λ.ptsSp.symm (fibreMap (abqFibre i) (ptsSp x)) =
        if i = 0 then (GluedPic0.toPic0Pair ssFinset x).1 else (GluedPic0.toPic0Pair ssFinset x).2

  torus_ptsSp : ∀ x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ssFinset,
      (∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) toricRank),
          NeronModelInfra.schemeHomOverComp y torusFibre = toFibrePt (ptsSp x)) ↔
        x ∈ (GluedPic0.nodeUnit ssFinset).range

  hecke_special_twist : ∀ (S : Set ℕ) (t : CohCarrier.Gen M S) (x : SchemeHomOver (resPt A ≫ Λ.σA) g),
      ∃ x' : SchemeHomOver (resPt A ≫ Λ.σA) g, (NeronModelInfra.schemeHomOverComp x (hecke S t)).1 = x'.1

  degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM))

  degeneracyHom : Fin 2 → SchemeHomOver g Λ.f
  degeneracyHom_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (degeneracyHom i) =
        Λ.L.mul s (NeronModelInfra.schemeHomOverComp x (degeneracyHom i))
          (NeronModelInfra.schemeHomOverComp y (degeneracyHom i))

  degeneracyHom_pts : ∀ (i : Fin 2) (x : JH M H),
      (Λ.pts (degPts i x)).1 = (pts x).1 ≫ (degeneracyHom i).1

  degeneracyHom_special : ∀ (ē : (ZMod (M / p))ˣ), ((ē : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
    haveI : NeZero (M / p) := neZero_div p M hpM
    ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) g,
      Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (degeneracyHom 0)) =
          Λ.ptsSp.symm (fibreMap (abqFibre 0) x) +
            qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (Λ.ptsSp.symm (fibreMap (abqFibre 1) x)) ∧
      Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp x (degeneracyHom 1)) =
          qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (Λ.ptsSp.symm (fibreMap (abqFibre 0) x)) +
            SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) ē)) •
              Λ.ptsSp.symm (fibreMap (abqFibre 1) x)

  toricLift : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA g)
  toricLift_isClosedImmersion : ∀ (m : ℕ) (hm : 0 < m), IsClosedImmersion (toricLift m hm).1
  toricLift_mul : ∀ (m : ℕ) (hm : 0 < m) (χ χ' : WithConv (muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ)),
      NeronModelInfra.schemeHomOverComp (muPt A toricRank m (χ * χ').ofConv) (toricLift m hm) =
        (L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ.ofConv) (toricLift m hm))
          (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ'.ofConv) (toricLift m hm))
  toricLift_compat : ∀ (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m'),
      muIncl ↥A toricRank h ≫ (toricLift m' hm').1 = (toricLift m hm).1
  toricLift_special : ∀ (m : ℕ) (hm : 0 < m),
      muBaseChange (residue ↥A) toricRank m ≫ (toricLift m hm).1 ≫ pullback.fst g Λ.σA =
        muToTorus (ResidueField ↥A) toricRank m ≫ torusFibre.1 ≫ pullback.fst g (resPt A ≫ Λ.σA)
  toricLift_inertia : ∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → σ ζ = ζ ^ c) →
      ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        σ • pts.symm (genOfBaseChangePt Λ.hσA
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
          c • pts.symm (genOfBaseChangePt Λ.hσA
            (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm)))
  toricLift_dec : ∀ (m : ℕ) (hm : 0 < m), ∀ σ ∈ A.decompositionSubgroup ℚ,
      ∀ χ : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        ∃ χ' : muCoord ↥A toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          σ • pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ) (toricLift m hm))) =
            pts.symm (genOfBaseChangePt Λ.hσA
              (NeronModelInfra.schemeHomOverComp (muPt A toricRank m χ') (toricLift m hm)))

attribute [nolint docBlame] JHNeronObjectAtP.separated JHNeronObjectAtP.locallyOfFiniteType
  JHNeronObjectAtP.quasiCompact JHNeronObjectAtP.surjective JHNeronObjectAtP.nsmul_surjective
  JHNeronObjectAtP.toricLift JHNeronObjectAtP.toricLift_isClosedImmersion JHNeronObjectAtP.toricLift_mul
  JHNeronObjectAtP.toricLift_compat JHNeronObjectAtP.toricLift_special JHNeronObjectAtP.toricLift_inertia
  JHNeronObjectAtP.toricLift_dec JHNeronObjectAtP.abqFibre_flat JHNeronObjectAtP.abqFibre_surjective
  JHNeronObjectAtP.abqFibre_mul JHNeronObjectAtP.degeneracyHom_mul

namespace JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : LevelData p M H hpM A}


end JHNeronObjectAtP

end ModularCurve

end
