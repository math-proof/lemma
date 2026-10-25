/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean -/

import Mathlib.Algebra.FreeAlgebra
import Theorem.NumberTheory.MultipleZeta.Index.Part2
import Lemma.Nat.MultipleZeta.Index
import Def.NumberTheory.MultipleZeta.WordAlgebra.Part2


namespace MetaMathlibExt.MultipleZeta

theorem zWord_eq_one_of_entries_eq_nil (idx : Index) (h : idx.entries = []) :
    zWord idx = 1 := by
  have hp : idx.pnatEntries = [] := by
    have hval := pnatEntries_val idx
    rw [h] at hval
    simpa using hval
  simp [zWord, zWordPNat, hp]

theorem zWordPNat_mem_hOne (l : List PNat) :
    zWordPNat l ∈ wordSubmonoidHOne := by
  induction l with
  | nil =>
    simp [zWordPNat, IsHOneWord, wordSubmonoidHOne]
  | cons k ks ih =>
    simp only [zWordPNat, List.map_cons, List.prod_cons]
    have hk : hoffmanBlock k ∈ wordSubmonoidHOne := by
      change IsHOneWord (hoffmanBlock k)
      refine Or.inr ⟨FreeMonoid.ofList (List.replicate (k.val - 1) false), ?_⟩
      simp only [hoffmanBlock, yWord]
      rw [FreeMonoid.ofList_append]
    exact wordSubmonoidHOne.mul_mem hk ih

theorem exists_hoffmanBlock_eq_xWord_mul_yWord (k : PNat) (hk : 2 ≤ k.val) :
    ∃ u, hoffmanBlock k = xWord * u * yWord := by
  refine ⟨FreeMonoid.ofList (List.replicate (k.val - 2) false), ?_⟩
  simp only [hoffmanBlock, xWord, yWord]
  have h1 : k.val - 1 = (k.val - 2) + 1 := by omega
  have h2 : List.replicate (k.val - 1) false =
      false :: List.replicate (k.val - 2) false := by
    rw [h1, List.replicate_succ]
  rw [h2, FreeMonoid.ofList_cons, FreeMonoid.ofList_append]
  simp [mul_assoc]

theorem hZero_word_mul_hOne_mem (ua : FreeMonoid Bool) (v : FreeMonoid Bool)
    (hv : v ∈ wordSubmonoidHOne) :
    xWord * ua * yWord * v ∈ wordSubmonoidHZero := by
  change IsHOneWord v at hv
  change IsHZeroWord (xWord * ua * yWord * v)
  rcases hv with rfl | ⟨ub, rfl⟩
  · exact Or.inr ⟨ua, by simp [mul_assoc]⟩
  · exact Or.inr ⟨ua * yWord * ub, by simp [mul_assoc]⟩

theorem zWord_mem_hZero (idx : Index) (h : IsHZeroIndex idx) :
    zWord idx ∈ wordSubmonoidHZero := by
  simp only [IsHZeroIndex] at h
  rcases h with hadm | hempty
  · cases hp : idx.pnatEntries with
    | nil =>
      have hval := pnatEntries_val idx
      rw [hp] at hval
      have hempty' : idx.entries = [] := by
        simpa using hval.symm
      rw [Index.isAdmissible_iff, hempty'] at hadm
      simp at hadm
    | cons k ks =>
      have hk2 : 2 ≤ k.val := by
        have hadmList : IsAdmissible idx.entries :=
          (Index.isAdmissible_iff idx).mp hadm
        have hentries : idx.entries = k.val :: ks.map PNat.val := by
          have hval := pnatEntries_val idx
          rw [hp] at hval
          simp at hval
          exact hval.symm
        rw [hentries] at hadmList
        simpa [IsAdmissible] using hadmList
      simp only [zWord, zWordPNat, hp, List.map_cons, List.prod_cons]
      obtain ⟨u, hu⟩ := exists_hoffmanBlock_eq_xWord_mul_yWord k hk2
      rw [hu]
      exact hZero_word_mul_hOne_mem u _ (zWordPNat_mem_hOne ks)
  · have hp : idx.pnatEntries = [] := by
      have hval := pnatEntries_val idx
      rw [hempty] at hval
      simpa using hval
    simp [zWord, zWordPNat, hp, wordSubmonoidHZero, IsHZeroWord]

theorem mem_range_mapDomainAlgHom_iff_support_subset
    (s : Submonoid (FreeMonoid Bool)) (a : MonoidAlgebra ℚ (FreeMonoid Bool)) :
    a ∈ (MonoidAlgebra.mapDomainAlgHom ℚ ℚ s.subtype).range ↔
      ∀ w ∈ a.coeff.support, w ∈ s := by
  classical
  simp only [AlgHom.mem_range, MonoidAlgebra.mapDomainAlgHom_apply]
  constructor
  · rintro ⟨b, rfl⟩ w hw
    change w ∈ (MonoidAlgebra.mapDomain s.subtype b).coeff.support at hw
    rw [MonoidAlgebra.coeff_mapDomain] at hw
    change w ∈
      (Finsupp.mapDomain (fun u : s => (u : FreeMonoid Bool)) b.coeff).support at hw
    rw [Finsupp.mapDomain_support_of_injective Subtype.coe_injective b.coeff] at hw
    simp only [Finset.mem_image] at hw
    obtain ⟨u, _, rfl⟩ := hw
    exact u.property
  · intro h
    refine ⟨MonoidAlgebra.comapDomain (fun u : s => (u : FreeMonoid Bool))
      Subtype.coe_injective a, ?_⟩
    apply MonoidAlgebra.mapDomain_comapDomain
    intro w hw
    exact ⟨⟨w, h w hw⟩, rfl⟩

theorem mem_hOne_iff_support_subset (a : FreeAlgebra ℚ Bool) :
    a ∈ hOne ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a).coeff.support,
        w ∈ wordSubmonoidHOne := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a ∈
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).range ↔ _
  exact mem_range_mapDomainAlgHom_iff_support_subset _ _

theorem mem_hZero_iff_support_subset (a : FreeAlgebra ℚ Bool) :
    a ∈ hZero ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a).coeff.support,
        w ∈ wordSubmonoidHZero := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) a ∈
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype).range ↔ _
  exact mem_range_mapDomainAlgHom_iff_support_subset _ _

theorem zMonomial_mem_hZero (idx : Index) (h : IsHZeroIndex idx) :
    zMonomial idx ∈ hZero := by
  rw [mem_hZero_iff_support_subset]
  simpa [zMonomial] using zWord_mem_hZero idx h

end MetaMathlibExt.MultipleZeta
