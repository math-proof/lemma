/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/TransferMatrixOfGRH.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.TransferMatrixOfGRH

namespace MetaMathlibExt

example : zykovZeroIndicator 0 = true := rfl
example : zykovZeroIndicator 1 = false := rfl

example : relationPairing (V := Fin 2) (W := Fin 2) (fun _ _ => True)
    (fun _ => true) (fun _ => true) = 4 := rfl

example :
    zykovTransferMatrix (⊥ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2))
      (fun _ _ => False)
      ((⟨∅, by simp⟩ :
          {s : Finset (Fin 2) // (⊥ : SimpleGraph (Fin 2)).IsIndepSet (↑s : Set (Fin 2))}),
        (⟨∅, by simp⟩ :
          {s : Finset (Fin 2) // (⊥ : SimpleGraph (Fin 2)).IsIndepSet (↑s : Set (Fin 2))})) =
      true := rfl

#print axioms zykovZeroIndicator
#print axioms independentSetCharacteristic
#print axioms relationPairing
#print axioms zykovTransferMatrix

end MetaMathlibExt
