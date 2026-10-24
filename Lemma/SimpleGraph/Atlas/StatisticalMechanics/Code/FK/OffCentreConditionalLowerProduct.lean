import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
open SimpleGraph StatMech StatMech.FK


/--
[ocd_freeMass_mul_outsideMass_le_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreConditionalLowerProduct.lean)
-/
@[path]
private lemma ocd_freeMass_mul_outsideMass_le_inter_eq
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  [DecidablePred bdryOut]
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (bdryOut : Vout → Prop)
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega) * (∑ rho, B.indicator (fun _ => (1 : Real)) rho * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q rho) ≤ ∑ rho, ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator (fun _ => (1 : Real)) rho * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q rho := by
-- proof
  apply StatMech.FK.ocd_freeMass_mul_outsideMass_le_inter Gin Gout ιV bdryOut hι hadjm hp hp1 hq hA hB

/--
[ocd_freeMass_mul_freeOutsideMass_le_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreConditionalLowerProduct.lean)
-/
@[path]
private lemma ocd_freeMass_mul_freeOutsideMass_le_inter_eq
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega) * (∑ rho, B.indicator (fun _ => (1 : Real)) rho * fkProb Gout p q rho) ≤ ∑ rho, ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator (fun _ => (1 : Real)) rho * fkProb Gout p q rho := by
-- proof
  apply StatMech.FK.ocd_freeMass_mul_freeOutsideMass_le_inter Gin Gout ιV hι hadjm hp hp1 hq hA hB


-- created on 2026-10-23
