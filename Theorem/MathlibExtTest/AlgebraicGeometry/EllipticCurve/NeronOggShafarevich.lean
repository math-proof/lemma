/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/NeronOggShafarevich.lean -/


import sympy.atlas.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich


namespace MetaMathlibExt

open scoped WeierstrassCurve.Affine

-- Prime-to-residue-characteristic torsion is fixed by every inertia element.
example (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (ksep : Type*) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] [DecidableEq ksep]
    (𝒪 : ValuationSubring ksep)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range)
    (σ : 𝒪.decompositionSubgroup k) (hσ : σ ∈ 𝒪.inertiaSubgroup k)
    (P : (E⁄ksep).Point) (hP : (n : ℤ) • P = 0) :
    WeierstrassCurve.Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P :=
  good_reduction_torsion_unramified R k E n ksep 𝒪 h𝒪 σ hσ P hP

end MetaMathlibExt
