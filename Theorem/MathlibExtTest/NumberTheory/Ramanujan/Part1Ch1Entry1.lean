/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch1Entry1.lean -/


import Lemma.Nat.Ramanujan.Part1Ch1Entry1


namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1

open MathlibExt.NumberTheory.Ramanujan.Part1Ch1.Entry1Magicsquare3

-- Boundary case `n = 1`: the common line-sum value is `5 + 7 = 12`.
example : ∃ S : ℕ, S = 12 := by
  have h := ramanujan_part1_ch1_entry1_magicsquare3
    (n := 1) (by decide : 0 < 1)
    (a := fun _ => 5) (b := fun _ => 7)
    (L := fun _ _ => (0 : Fin 1)) (R := fun _ _ => (0 : Fin 1))
    (fun i => bijective_fin1 _) (fun j => bijective_fin1 _)
    (bijective_fin1 _) (bijective_fin1 _)
    (fun i => bijective_fin1 _) (fun j => bijective_fin1 _)
    (bijective_fin1 _) (bijective_fin1 _)
    (bijective_fin1_prod _)
  obtain ⟨S, hrow, hcol, hdiag, hanti⟩ := h
  have h0 := hrow 0
  have h1 := hcol 0
  simp at h0 h1 hdiag hanti
  exact ⟨S, by omega⟩

-- Boundary case `n = 1`: the diagonal and anti-diagonal sums give `3 + 4 = 7`.
example : ∃ S : ℕ, S = 7 := by
  have h := ramanujan_part1_ch1_entry1_magicsquare3
    (n := 1) (by decide : 0 < 1)
    (a := fun _ => 3) (b := fun _ => 4)
    (L := fun _ _ => (0 : Fin 1)) (R := fun _ _ => (0 : Fin 1))
    (fun i => bijective_fin1 _) (fun j => bijective_fin1 _)
    (bijective_fin1 _) (bijective_fin1 _)
    (fun i => bijective_fin1 _) (fun j => bijective_fin1 _)
    (bijective_fin1 _) (bijective_fin1 _)
    (bijective_fin1_prod _)
  obtain ⟨S, -, -, hdiag, hanti⟩ := h
  simp at hdiag hanti
  exact ⟨S, by omega⟩

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch1Entry1
