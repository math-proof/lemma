/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Theorem.RepresentationTheory.Homological.TateCohomology.FiniteCyclic.Part3
@[expose] noncomputable section

open CategoryTheory Limits ModuleCat Rep


namespace TateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

variable (A : Rep R G)

noncomputable def negOneIso (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-1) ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology :=
  negOneBridge A ≪≫
    (negOneSC A).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (negOneSC_range_eq A g hg)).toModuleIso ≪≫
    (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso.symm

noncomputable def positivePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) [NeZero i] :
    tateCohomology A (i : ℤ) ≅ tateCohomology A ((i + 2 : ℕ) : ℤ) := by
  letI : NeZero (i + 2) := ⟨by omega⟩
  by_cases hi : Even i
  · have h2 : Even (i + 2) := hi.add even_two
    simpa using ((isoGroupCohomology (R := R) (G := G) i).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg i hi ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg (i + 2) h2).symm ≪≫
      ((isoGroupCohomology (R := R) (G := G) (i + 2)).app A).symm)
  · have ho : Odd i := Nat.not_even_iff_odd.mp hi
    have ho2 : Odd (i + 2) := ho.add_even even_two
    simpa using ((isoGroupCohomology (R := R) (G := G) i).app A ≪≫
      Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg i ho ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg (i + 2) ho2).symm ≪≫
      ((isoGroupCohomology (R := R) (G := G) (i + 2)).app A).symm)

noncomputable def negativePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) :
    tateCohomology A (-(i + 4 : ℤ)) ≅ tateCohomology A (-(i + 2 : ℤ)) := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero (i + 3) := ⟨by omega⟩
  letI : NeZero (i + 1) := ⟨by omega⟩
  by_cases h : Even (i + 1)
  · have h3 : Even (i + 3) := by simpa [Nat.add_assoc] using h.add even_two
    exact ((TateCohomology.isoGroupHomology (-(i + 4 : ℤ)) (i + 3) (by omega)).app A ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg (i + 3) h3 ≪≫
      (Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg (i + 1) h).symm ≪≫
      ((TateCohomology.isoGroupHomology (-(i + 2 : ℤ)) (i + 1) (by omega)).app A).symm)
  · have ho : Odd (i + 1) := Nat.not_even_iff_odd.mp h
    have ho3 : Odd (i + 3) := by simpa [Nat.add_assoc] using ho.add_even even_two
    exact ((TateCohomology.isoGroupHomology (-(i + 4 : ℤ)) (i + 3) (by omega)).app A ≪≫
      Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg (i + 3) ho3 ≪≫
      (Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg (i + 1) ho).symm ≪≫
      ((TateCohomology.isoGroupHomology (-(i + 2 : ℤ)) (i + 1) (by omega)).app A).symm)

noncomputable def zeroPeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A 0 ≅ tateCohomology A 2 := by
  letI : NeZero 2 := ⟨by omega⟩
  simpa using (zeroIso A g hg ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm ≪≫
    ((isoGroupCohomology (R := R) (G := G) 2).app A).symm)

noncomputable def negOnePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-1) ≅ tateCohomology A 1 := by
  letI : NeZero 1 := ⟨by omega⟩
  simpa using (negOneIso A g hg ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm ≪≫
    ((isoGroupCohomology (R := R) (G := G) 1).app A).symm)

noncomputable def negTwoPeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-2) ≅ tateCohomology A 0 := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero 1 := ⟨by omega⟩
  simpa using (((isoGroupHomology (R := R) (G := G) (-2) 1 (by omega)).app A) ≪≫
    Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg 1 odd_one ≪≫
    (zeroIso A g hg).symm)

noncomputable def negThreePeriodicityIso (A : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology A (-3) ≅ tateCohomology A (-1) := by
  letI : DecidableEq G := Classical.decEq G
  letI : NeZero 2 := ⟨by omega⟩
  simpa using (((isoGroupHomology (R := R) (G := G) (-3) 2 (by omega)).app A) ≪≫
    Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg 2 even_two ≪≫
    (negOneIso A g hg).symm)

end TateCohomology
