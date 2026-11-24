module
public import Mathlib
public import Def.ModularCurve_JZeroNeronObjectAtP
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Theorem.Scheme.NeronSpecialFibreRestriction
public import Lemma.CuspForm.XHDifferentialsModL
public import Theorem.UpperHalfPlane.XHOperators
public import Theorem.ResidueField.GluedPic0
public import Def.GaloisRep_Flat
public import Def.FLTPrelim_Ramification
public import Instance.ModularCurve_JHNeronObjectAtP
public import Structure.ModularCurve_JHNeronObjectAtP
public import Abbrev.ModularCurve_JHNeronObjectAtP
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing
open ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups


public section

noncomputable section

namespace ModularCurve

namespace JHNeronObjectAtP


end JHNeronObjectAtP

open JHNeronObjectAtP in


namespace JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : LevelData p M H hpM A}

def toricPoint (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) : JH M H :=
  O.pts.symm (genOfBaseChangePt Λ.hσA
    (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm)))

def toricPts (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : AddSubgroup (JH M H) :=
  if hm : 0 < m then AddSubgroup.closure (Set.range (O.toricPoint m hm)) else ⊥

def finPts (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : AddSubgroup (JH M H) :=
  AddSubgroup.closure {x | x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m ∧ ExtendsToPlace A Λ.σA (O.pts x)}

def Pts (O : JHNeronObjectAtP p M H hpM A hA Λ) : Type := SchemeHomOver (genPt p) O.g

def ptsAddEquiv (O : JHNeronObjectAtP p M H hpM A hA Λ) : JH M H ≃+ O.Pts :=
  ((show O.Pts ≃ JH M H from O.pts.symm).addEquiv).symm

end JHNeronObjectAtP

end ModularCurve

end
