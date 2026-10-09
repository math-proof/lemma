import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich

open scoped WeierstrassCurve.Affine

/--
[good_reduction_torsion_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/NeronOggShafarevich.lean)
-/
@[path]
private lemma good_reduction_torsion_unramified_eq
-- given
  (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
  (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
  (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
  (ksep : Type*) [Field ksep] [Algebra k ksep]
  [IsSepClosure k ksep] [DecidableEq ksep]
  (𝒪 : ValuationSubring ksep)
  (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
-- imply
  (∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P : (E⁄ksep).Point, (n : ℤ) • P = 0 →
    WeierstrassCurve.Affine.Point.map (σ : AlgEquiv k ksep ksep).toAlgHom P = P) :=
-- proof
  MetaMathlibExt.good_reduction_torsion_unramified R k E n ksep 𝒪 h𝒪


-- created on 2026-10-09
