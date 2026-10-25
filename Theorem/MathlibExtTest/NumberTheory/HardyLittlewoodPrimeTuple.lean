/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HardyLittlewoodPrimeTuple.lean -/


import Def.NumberTheory.HardyLittlewoodPrimeTuple


namespace MetaMathlibExt

noncomputable section

example : hardyLittlewoodResidueCount 0 Fin.elim0 2 = 0 := by decide

example : hardyLittlewoodResidueCount 2 (fun i => (i.val : ℤ)) 2 = 2 := by decide

#print axioms hardyLittlewoodResidueCount
#print axioms hardyLittlewoodPrimeTupleCount
#print axioms hardyLittlewoodSingularSeries

end
end MetaMathlibExt
