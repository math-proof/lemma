import Structure.ModularCurve_FullLevelSemistableCovering
import Lemma.AlgebraicCurve.SemistableChartsComap
import Structure.AlgebraicCurve_ConstantReduction
import Abbrev.DrinfeldCurve_FunctionField
import Def.GaloisRep_TameCharacter
import Def.FLTPrelim_Ramification
import Instance.ModularCurve_ArithmeticGalois

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing DrinfeldCurve CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

abbrev _root_.DrinfeldCurve.quotField (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2))) :
    IntermediateField κ (drinfeldFunctionField q κ) :=
  IntermediateField.fixedField (Subgroup.closure (Set.range fun ζ : ↥C =>
    hFunctionFieldAction q κ ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q ζ⟩))

end ModularCurve.FullLevel.SemistableCovering

end
