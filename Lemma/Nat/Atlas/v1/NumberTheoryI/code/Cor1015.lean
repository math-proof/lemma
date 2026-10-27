import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.Cor1015
open Polynomial IsLocalRing Ideal


/--
[minpoly_irreducible_of_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma minpoly_irreducible_of_dvr
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B} :
-- imply
  Irreducible (minpoly A α) :=
-- proof
  (minpoly.prime_of_isIntegrallyClosed (IsIntegral.of_finite A α)).irreducible

/--
[residue_separable_of_irred_sep_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma residue_separable_of_irred_sep_reduction
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B}
-- given
  (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
  (hirred : Irreducible (reducedMinpoly A B α))
  (hsep : (reducedMinpoly A B α).Separable) :
-- imply
  Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
-- proof
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def
  have hne : minpoly A α ≠ 0 := by
    intro h
    have : gbar = 0 := by rw [hgbar_def, reducedMinpoly, h, Polynomial.map_zero]
    exact hirred.ne_zero this
  have hint : IsIntegral A α := minpoly.ne_zero_iff.mp hne
  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα
  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]
    simp [minpoly.aeval]
  have hmon_gbar : gbar.Monic := (minpoly.monic hint).map (residue A)
  have heq : gbar = minpoly k abar := minpoly.eq_of_irreducible_of_monic hirred heval hmon_gbar
  have hsep_abar : IsSeparable k abar := by
    unfold IsSeparable
    rwa [← heq]
  have hmem : abar ∈ separableClosure k l :=
    mem_separableClosure_iff.mpr hsep_abar
  have hle : Algebra.adjoin k ({abar} : Set l) ≤
    (separableClosure k l).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem)
  have htop : separableClosure k l = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj, IntermediateField.top_toSubalgebra]
    exact top_le_iff.mp (hres_top ▸ hle)
  rwa [separableClosure.eq_top_iff] at htop

/--
[finrank_eq_of_irred_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma finrank_eq_of_irred_reduction
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B}
-- given
  (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
  (hirred : Irreducible (reducedMinpoly A B α)) :
-- imply
  Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B) := by
-- proof
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def
  have hint : IsIntegral A α := IsIntegral.of_finite A α
  have hmon := minpoly.monic hint
  have hmon_gbar : gbar.Monic := hmon.map (residue A)
  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]; simp [minpoly.aeval]
  have hintk : IsIntegral k abar :=
    ⟨gbar, hmon_gbar, heval⟩
  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα
  have heq : gbar = minpoly k abar := minpoly.eq_of_irreducible_of_monic hirred heval hmon_gbar
  let pbA := PowerBasis.ofAdjoinEqTop' hint hα
  let pbk := PowerBasis.ofAdjoinEqTop' hintk hres_top
  calc Module.finrank A B
    = pbA.dim := pbA.finrank
    _ = (minpoly A α).natDegree := PowerBasis.ofAdjoinEqTop'_dim hint hα
    _ = gbar.natDegree := (hmon.natDegree_map (residue A)).symm
    _ = (minpoly k abar).natDegree := by rw [heq]
    _ = pbk.dim := (PowerBasis.ofAdjoinEqTop'_dim hintk hres_top).symm
    _ = Module.finrank k l := pbk.finrank.symm

/--
[reduced_minpoly_separable_of_separable_residue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma reduced_minpoly_separable_of_separable_residue
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B}
-- given
  (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
  (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
  (hdeg : Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) :
-- imply
  (reducedMinpoly A B α).Separable := by
-- proof
  set k := ResidueField A
  set l := ResidueField B
  set abar := residue B α
  set gbar := reducedMinpoly A B α with hgbar_def
  have hint : IsIntegral A α := IsIntegral.of_finite A α
  have hmon := minpoly.monic hint
  have hmon_gbar : gbar.Monic := hmon.map (residue A)
  have heval : Polynomial.aeval abar gbar = 0 := by
    show Polynomial.aeval (residue B α) ((minpoly A α).map (residue A)) = 0
    rw [← residue_aeval_eq]; simp [minpoly.aeval]
  have hintk : IsIntegral k abar := ⟨gbar, hmon_gbar, heval⟩
  have hres_top : Algebra.adjoin k ({abar} : Set l) = ⊤ := adjoin_residue_top_of_adjoin_top α hα
  have hdvd : minpoly k abar ∣ gbar := minpoly.dvd k abar heval
  have hdeg_gbar : gbar.natDegree = (minpoly A α).natDegree := hmon.natDegree_map (residue A)
  let pbA := PowerBasis.ofAdjoinEqTop' hint hα
  let pbk := PowerBasis.ofAdjoinEqTop' hintk hres_top
  have hfin_l : Module.finrank k l = (minpoly k abar).natDegree := by
    rw [pbk.finrank, PowerBasis.ofAdjoinEqTop'_dim]
  have hfin_A : Module.finrank A B = (minpoly A α).natDegree := by
    rw [pbA.finrank, PowerBasis.ofAdjoinEqTop'_dim]
  have hdeg_eq : gbar.natDegree = (minpoly k abar).natDegree := by
    rw [hdeg_gbar, ← hfin_A, hdeg, hfin_l]
  have heq : gbar = minpoly k abar :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintk) hmon_gbar hdvd
      (le_of_eq hdeg_eq)
  have hsep_abar : (minpoly k abar).Separable := Algebra.IsSeparable.isSeparable k abar
  rw [heq]; exact hsep_abar

/--
[reduced_minpoly_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma reduced_minpoly_irreducible
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B}
-- given
  (hsep : (reducedMinpoly A B α).Separable) :
-- imply
  Irreducible (reducedMinpoly A B α) := by
-- proof
  have hirr := minpoly_irreducible_of_dvr A B α
  have hmon := minpoly.monic (IsIntegral.of_finite A α)
  have hdeg_pos : 0 < (reducedMinpoly A B α).natDegree := by
    rw [show reducedMinpoly A B α = (minpoly A α).map (residue A) from rfl,
      hmon.natDegree_map]
    exact minpoly.natDegree_pos (IsIntegral.of_finite A α)
  have hnu : ¬ IsUnit (reducedMinpoly A B α) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  constructor
  · exact hnu
  · intro p q hpq
    have hcop : IsCoprime p q := by
      rwa [hpq] at hsep
    exact irreducible_no_coprime_factor_mod hirr p q hpq hcop
set_option linter.unusedSectionVars false in

/--
[cor_10_15_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma cor_10_15_forward
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsUnramifiedDVRExtension A B]
  [FiniteDimensional (ResidueField A) (ResidueField B)] :
-- imply
  ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ ∧ (reducedMinpoly A B α).Separable := by
-- proof
  have hsep := IsUnramifiedDVRExtension.residue_separable (A := A) (B := B)
  have hdeg := IsUnramifiedDVRExtension.degree_eq (A := A) (B := B)
  obtain ⟨α, hα⟩ := dvr_monogenicity A B hsep
  exact ⟨α, hα, reduced_minpoly_separable_of_separable_residue A B α hα hsep hdeg⟩
set_option linter.unusedSectionVars false in

/--
[cor_10_15_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma cor_10_15_reverse
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {α : B}
-- given
  (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
  (hsep_red : (reducedMinpoly A B α).Separable) :
-- imply
  IsUnramifiedDVRExtension A B := by
-- proof
  have hirred := reduced_minpoly_irreducible A B α hsep_red
  exact {
    residue_separable := residue_separable_of_irred_sep_reduction A B α hα hirred hsep_red
    degree_eq := finrank_eq_of_irred_reduction A B α hα hirred
  }

/--
[cor_10_15](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma cor_10_15
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (ResidueField A) (ResidueField B)] :
-- imply
  IsUnramifiedDVRExtension A B ↔ ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ ∧ (reducedMinpoly A B α).Separable := by
-- proof
  constructor
  · intro h
    exact cor_10_15_forward A B
  · rintro ⟨α, hα, hsep⟩
    exact cor_10_15_reverse A B α hα hsep
section Cor_10_16
variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
omit [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing B]
  [IsLocalHom (algebraMap A B)] [Module.Finite A B] in

/--
[minpoly_reduction_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma minpoly_reduction_separable
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {n : ℕ}
  {ζ : B}
-- given
  (hζ_int : IsIntegral A ζ)
  (hζ : ζ ^ n = 1)
  (hn : (n : ResidueField A) ≠ 0) :
-- imply
  ((minpoly A ζ).map (residue A)).Separable := by
-- proof
  haveI : IsIntegrallyClosed A := GCDMonoid.toIsIntegrallyClosed
  have hdvd : minpoly A ζ ∣ X ^ n - C 1 :=
    minpoly.isIntegrallyClosed_dvd hζ_int (by simp [hζ])
  have hdvd_bar : (minpoly A ζ).map (residue A) ∣
    (X ^ n - C 1 : A[X]).map (residue A) :=
    Polynomial.map_dvd _ hdvd
  have hmap : (X ^ n - C 1 : A[X]).map (residue A) = X ^ n - C 1 := by
    simp [Polynomial.map_sub, Polynomial.map_pow, map_X, map_one]
  rw [hmap] at hdvd_bar
  have hsep : (X ^ n - C (1 : ResidueField A)).Separable :=
    separable_X_pow_sub_C 1 hn one_ne_zero
  exact hsep.of_dvd hdvd_bar

/--
[cyclotomic_extension_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma cyclotomic_extension_unramified
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {n : ℕ}
  {ζ : B}
-- given
  (hprim : IsPrimitiveRoot ζ n)
  (hn : (n : ResidueField A) ≠ 0)
  (hgen : Algebra.adjoin A ({ζ} : Set B) = ⊤) :
-- imply
  IsUnramifiedDVRExtension A B :=
-- proof
  cor_10_15_reverse A B ζ hgen
    (minpoly_reduction_separable A B (IsIntegral.of_finite A ζ) hprim.pow_eq_one hn)

/--
[cor_10_16_of_adjoin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015.lean)
-/
@[path]
lemma cor_10_16_of_adjoin
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {n : ℕ}
  {ζ : B}
-- given
  (hprim : IsPrimitiveRoot ζ n)
  (hcoprime : Nat.Coprime n (ringChar (IsLocalRing.ResidueField A)))
  (hgen : Algebra.adjoin A ({ζ} : Set B) = ⊤) :
-- imply
  IsUnramifiedDVRExtension A B := by
-- proof
  apply cyclotomic_extension_unramified A B hprim _ hgen
  intro h
  have hchar : ringChar (IsLocalRing.ResidueField A) ∣ n :=
    (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A)
      (ringChar (IsLocalRing.ResidueField A)) n).mp h
  have h1 : ringChar (IsLocalRing.ResidueField A) = 1 := hcoprime.symm.eq_one_of_dvd hchar
  haveI : CharP (IsLocalRing.ResidueField A) 1 := h1 ▸ ringChar.charP (IsLocalRing.ResidueField A)
  exact @CharP.false_of_nontrivial_of_char_one (IsLocalRing.ResidueField A) _ _ ‹_›
end Cor_10_16


-- created on 2026-10-23
