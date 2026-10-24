/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/CoveringSystem/ExactCover.lean -/


import sympy.atlas.NumberTheory.CoveringSystem.ExactCover

example : Int.indexedCoverMultiplicity (fun _ : Fin 2 => 2)
    (fun i => (i : ℕ)) 0 = 1 := by decide

example {k M : ℕ} {moduli : Fin k → ℕ} {residues : Fin k → ℤ} {target : Set ℤ}
    (h : Int.IsExactCoverOf moduli residues M target) : 2 ≤ k :=
  h.1
