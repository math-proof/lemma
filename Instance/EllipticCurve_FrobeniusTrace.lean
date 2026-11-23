-- Carved from Lemma/Definitions/Def_EllipticCurve_FrobeniusTrace.lean: instance decls only.
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_Ramification
@[expose] public section

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

end WeierstrassCurve.Affine.Point


end
