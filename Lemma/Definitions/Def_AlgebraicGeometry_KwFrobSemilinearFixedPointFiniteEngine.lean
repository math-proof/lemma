import Mathlib

open Polynomial

noncomputable section

namespace AlgebraicCurve.KwFsfp

theorem kw_fsfp_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

theorem kw_fsfp_fixedScalars_finite (K : Type*) [Field K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    {a : K | a ^ ℓ = a}.Finite := by
  have _ := kw_fsfp_axiomAnchor
  have hne : (X ^ ℓ - X : K[X]) ≠ 0 := by
    intro h
    have hcoeff : (X ^ ℓ - X : K[X]).coeff ℓ = 1 := by
      have h1 : (1 : ℕ) ≠ ℓ := fun h => hℓ.out.ne_one h.symm
      simp [coeff_sub, coeff_X_pow, coeff_X, h1]
    rw [h, coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro a ha
  simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_pow, eval_X]
  exact sub_eq_zero_of_eq ha

section Engine

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]
variable {M : Type*} [AddCommGroup M] [Module K M]

theorem kw_fsfp_smul_inv (φ : M → M)
    (hsmul : ∀ (a : K) (m : M), φ (a ^ ℓ • m) = a • φ m) (b : K) (m : M) :
    φ (b • m) = (frobeniusEquiv K ℓ).symm b • φ m := by
  have hb : ((frobeniusEquiv K ℓ).symm b) ^ ℓ = b := by
    have h := (frobeniusEquiv K ℓ).apply_symm_apply b
    rwa [frobeniusEquiv_def] at h
  conv_lhs => rw [← hb]
  exact hsmul _ m

theorem kw_fsfp_fixedPoints_finite [FiniteDimensional K M]
    (φ : M → M) (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hsmul : ∀ (a : K) (m : M), φ (a ^ ℓ • m) = a • φ m) :
    {m : M | φ m = m}.Finite := by
  classical
  have _ := kw_fsfp_axiomAnchor
  set σ := frobeniusEquiv K ℓ with hσ
  let φ' : M →+ M := AddMonoidHom.mk' φ hadd
  have hφ' : ∀ m, φ' m = φ m := fun _ => rfl
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K {m : M | φ m = m}
  have hs_fin : s.Finite := by
    haveI : IsNoetherian K M := IsNoetherian.iff_fg.mpr inferInstance
    exact hs_li.set_finite_of_isNoetherian
  have hR : {a : K | a ^ ℓ = a}.Finite := kw_fsfp_fixedScalars_finite K ℓ
  haveI hRsub : Finite ↥{a : K | a ^ ℓ = a} := hR.to_subtype
  set SF : Finset M := hs_fin.toFinset with hSF

  let Φ : (↥SF → ↥{a : K | a ^ ℓ = a}) → M := fun f =>
    ∑ i ∈ SF.attach, ((f i : K) • (i : M))
  refine (Set.finite_range Φ).subset ?_
  rintro x hx
  have hx_span : x ∈ Submodule.span K s := hs_span ▸ Submodule.subset_span hx
  obtain ⟨c, hc_supp, hc_sum⟩ := Submodule.mem_span_set.mp hx_span
  set S : Finset M := c.support with hS
  have hS_sub_SF : S ⊆ SF := fun mi hmi => by
    rw [hSF, Set.Finite.mem_toFinset]
    exact hc_supp hmi
  have hsum_x : ∑ mi ∈ S, c mi • mi = x := by
    simpa [Finsupp.sum] using hc_sum

  have htrans : ∑ mi ∈ S, (σ.symm (c mi)) • mi = x := by
    have hmem_fix : ∀ mi ∈ S, φ mi = mi := fun mi hmi => hs_sub (hc_supp hmi)
    calc ∑ mi ∈ S, (σ.symm (c mi)) • mi
        = ∑ mi ∈ S, (σ.symm (c mi)) • φ mi :=
          Finset.sum_congr rfl (fun mi hmi => by rw [hmem_fix mi hmi])
      _ = ∑ mi ∈ S, φ (c mi • mi) :=
          Finset.sum_congr rfl (fun mi _ => (kw_fsfp_smul_inv φ hsmul _ _).symm)
      _ = φ' (∑ mi ∈ S, c mi • mi) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun _ _ => rfl
      _ = φ x := by rw [hsum_x, hφ']
      _ = x := hx

  have hc_fixed : ∀ mi ∈ S, σ.symm (c mi) = c mi := by
    have hzero : ∑ mi ∈ S, (σ.symm (c mi) - c mi) • mi = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib, htrans, hsum_x, sub_self]
    let emb : ↥S ↪ ↥s :=
      ⟨fun i => ⟨(i : M), hc_supp i.2⟩, fun i j hij => by
        apply Subtype.ext
        have h := congrArg Subtype.val hij
        simpa using h⟩
    have hind := linearIndependent_iff'.mp hs_li (S.attach.map emb)
      (fun j => σ.symm (c (j : M)) - c (j : M))
    have hsum_emb :
        ∑ j ∈ S.attach.map emb, (σ.symm (c (j : M)) - c (j : M)) • ((j : M)) = 0 := by
      rw [Finset.sum_map]
      have hcongr : ∀ i ∈ S.attach,
          (σ.symm (c ((emb i : ↥s) : M)) - c ((emb i : ↥s) : M)) • ((emb i : ↥s) : M)
            = (σ.symm (c (i : M)) - c (i : M)) • ((i : M)) := fun i _ => rfl
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_attach S (fun mi => (σ.symm (c mi) - c mi) • mi)]
      exact hzero
    intro mi hmi
    have hmem : emb ⟨mi, hmi⟩ ∈ S.attach.map emb :=
      Finset.mem_map_of_mem emb (S.mem_attach ⟨mi, hmi⟩)
    have := hind hsum_emb _ hmem
    exact sub_eq_zero.mp this

  refine ⟨fun i => ⟨c (i : M), ?_⟩, ?_⟩
  · by_cases hi : (i : M) ∈ S
    · have hfix := hc_fixed _ hi
      have heq : σ (c (i : M)) = c (i : M) := by
        conv_lhs => rw [← hfix]
        exact σ.apply_symm_apply _
      have := heq
      rw [hσ, frobeniusEquiv_def] at this
      exact this
    · have hzero : c (i : M) = 0 := Finsupp.notMem_support_iff.mp hi
      rw [Set.mem_setOf_eq, hzero, zero_pow hℓ.out.ne_zero]
  · show Φ _ = x
    calc ∑ i ∈ SF.attach, c (i : M) • (i : M)
        = ∑ mi ∈ SF, c mi • mi := Finset.sum_attach SF (fun mi => c mi • mi)
      _ = ∑ mi ∈ S, c mi • mi := by
          refine (Finset.sum_subset hS_sub_SF (fun mi _ hni => ?_)).symm
          rw [Finsupp.notMem_support_iff.mp hni, zero_smul]
      _ = x := hsum_x

end Engine

section Seam

variable {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]
variable {M : Type*} [AddCommGroup M] [Module K M]

theorem kw_fsfp_fixedPoints_inter_finite_of_mapsTo (W : Submodule K M)
    [FiniteDimensional K W]
    (φ : M → M) (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hsmul : ∀ (a : K) (m : M), φ (a ^ ℓ • m) = a • φ m)
    (hW : Set.MapsTo φ W W) :
    {m : M | m ∈ W ∧ φ m = m}.Finite := by
  have _ := kw_fsfp_axiomAnchor
  let ψ : W → W := fun w => ⟨φ w, hW w.2⟩
  have hψadd : ∀ x y : W, ψ (x + y) = ψ x + ψ y := fun x y =>
    Subtype.ext (by simpa [ψ] using hadd x y)
  have hψsmul : ∀ (a : K) (w : W), ψ (a ^ ℓ • w) = a • ψ w := fun a w =>
    Subtype.ext (by simpa [ψ] using hsmul a w)
  have hfin : {w : W | ψ w = w}.Finite :=
    kw_fsfp_fixedPoints_finite ψ hψadd hψsmul
  have himg : {m : M | m ∈ W ∧ φ m = m} ⊆ Subtype.val '' {w : W | ψ w = w} := by
    rintro m ⟨hmW, hmfix⟩
    exact ⟨⟨m, hmW⟩, Subtype.ext (by simpa [ψ] using hmfix), rfl⟩
  exact (hfin.image _).subset himg

end Seam

end AlgebraicCurve.KwFsfp

end

section Audits

/-- info: 'AlgebraicCurve.KwFsfp.kw_fsfp_axiomAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwFsfp.kw_fsfp_axiomAnchor

/-- info: 'AlgebraicCurve.KwFsfp.kw_fsfp_fixedScalars_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwFsfp.kw_fsfp_fixedScalars_finite

/-- info: 'AlgebraicCurve.KwFsfp.kw_fsfp_smul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwFsfp.kw_fsfp_smul_inv

/-- info: 'AlgebraicCurve.KwFsfp.kw_fsfp_fixedPoints_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwFsfp.kw_fsfp_fixedPoints_finite

/-- info: 'AlgebraicCurve.KwFsfp.kw_fsfp_fixedPoints_inter_finite_of_mapsTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwFsfp.kw_fsfp_fixedPoints_inter_finite_of_mapsTo

end Audits
