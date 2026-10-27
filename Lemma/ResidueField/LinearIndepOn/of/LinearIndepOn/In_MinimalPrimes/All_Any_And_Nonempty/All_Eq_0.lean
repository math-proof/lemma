import Mathlib
import Initialize.Tactic.Attr.Basic


private def PR
  (k : Type u) [Field k] (p : ℕ) (C : Type u) [CommRing C] [Algebra k C] :
  Prop :=
  ∀ (n : ℕ) (a : Fin n → k) (y : Fin n → C),
    (∀ d : Fin n → k, ∑ j, d j ^ p * a j = 0 → d = 0) → ∑ j, a j • y j ^ p = 0 → y = 0

private lemma PR.of_injective
  {k : Type u} [Field k]
  {C D : Type u} [CommRing C] [Algebra k C] [CommRing D] [Algebra k D]
  {p : ℕ}
  (f : C →ₐ[k] D)
-- given
  (hf : Function.Injective f)
  (h : PR k p D) :
-- imply
  PR k p C := by
-- proof
  intro n a y hind hsum
  have : (fun j => f (y j)) = 0 := by
    apply h n a _ hind
    have := congrArg f hsum
    rw [map_sum, map_zero] at this
    simpa only [map_smul, map_pow] using this
  funext j
  apply hf
  have hj := congrFun this j
  simp only [Pi.zero_apply] at hj
  rw [hj, Pi.zero_apply, map_zero]

private lemma PR.of_dense
  {k : Type u} [Field k]
  {B : Type u} [CommRing B] [Algebra k B]
  {p : ℕ}
  (S : Set (PrimeSpectrum B))
-- given
  (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
  (hS : ∀ 𝔰 ∈ S, PR k p 𝔰.asIdeal.ResidueField) :
-- imply
  PR k p B := by
-- proof
  intro n a y hind hsum
  funext j
  apply hdense
  intro 𝔰 h𝔰
  have h := hS 𝔰 h𝔰 n a (fun j => algebraMap B 𝔰.asIdeal.ResidueField (y j)) hind (by have := congrArg (IsScalarTower.toAlgHom k B 𝔰.asIdeal.ResidueField) hsum; rw [map_sum, map_zero] at this; simpa only [map_smul, map_pow, IsScalarTower.coe_toAlgHom'] using this)
  have hj := congrFun h j
  simp only [Pi.zero_apply] at hj
  apply Ideal.algebraMap_residueField_eq_zero.mp hj

private lemma PR.localization
  {k : Type u} [Field k]
  {B : Type u} [CommRing B] [Algebra k B]
  {p : ℕ}
-- given
  (hp : 0 < p)
  (h : PR k p B)
  (M : Submonoid B)
  (L : Type u) [CommRing L] [Algebra B L] [Algebra k L] [IsScalarTower k B L] [IsLocalization M L] :
-- imply
  PR k p L := by
-- proof
  intro n a y hind hsum
  classical
  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples_of_finite M y
  choose b hb using hu
  have h1 : algebraMap B L (∑ j, a j • b j ^ p) = 0 := by
    have e1 : (IsScalarTower.toAlgHom k B L) (∑ j, a j • b j ^ p) =
        ∑ j, algebraMap B L u ^ p * (a j • y j ^ p) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_pow, IsScalarTower.coe_toAlgHom', hb j, Algebra.smul_def (↑u : B),
        mul_pow, ← mul_smul_comm]
    rw [IsScalarTower.coe_toAlgHom'] at e1
    rw [e1, ← Finset.mul_sum, hsum, mul_zero]
  obtain ⟨v, hv⟩ := (IsLocalization.map_eq_zero_iff M L _).mp h1
  have h2 : ∑ j, a j • ((v : B) * b j) ^ p = 0 := by
    have e2 : ∀ j, a j • ((v : B) * b j) ^ p = (v : B) ^ p * (a j • b j ^ p) := by
      intro j
      rw [mul_pow, ← mul_smul_comm]
    simp only [e2]
    rw [← Finset.mul_sum]
    calc
      _ = (v : B) ^ (p - 1) * ((v : B) * ∑ j, a j • b j ^ p) := by
        rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
      _ = 0 := by rw [hv, mul_zero]
  have h3 := h n a (fun j => (v : B) * b j) hind h2
  funext j
  have hj : (v : B) * b j = 0 := congrFun h3 j
  have : algebraMap B L v * algebraMap B L (b j) = 0 := by
    rw [← map_mul, hj, map_zero]
  rwa [hb j, Algebra.smul_def (↑u : B), (IsLocalization.map_units L v).mul_right_eq_zero,
    (IsLocalization.map_units L u).mul_right_eq_zero] at this

private lemma PR.of_field
  {k : Type u} [Field k]
  (K : Type u) [Field K] [Algebra k K]
  {p : ℕ}
-- given
  (hp : p.Prime) [CharP K p]
  (HK : ∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K)) :
-- imply
  PR k p K := by
-- proof
  intro n a y hind hsum
  classical
  have : Fact p.Prime := ⟨hp⟩
  let V : Submodule k K := Submodule.span k (Set.range y)
  have : Module.Finite k V := Module.Finite.span_of_finite k (Set.finite_range y)
  let bV := Module.finBasis k V
  let w : Fin (Module.finrank k V) → K := fun i => (bV i : K)
  have hw : LinearIndependent k w := bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hwinj : Function.Injective w := hw.injective
  have hwp : LinearIndependent k (fun i => w i ^ p) := by
    have h1 : LinearIndepOn k _root_.id ((Finset.univ.image w : Finset K) : Set K) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      apply hw.linearIndepOn_id
    have h2 := HK _ h1
    rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff hwinj] at h2
  have hyV : ∀ j, y j ∈ V := fun j => Submodule.subset_span ⟨j, rfl⟩
  let μ : Fin n → Fin (Module.finrank k V) → k := fun j i => bV.repr ⟨y j, hyV j⟩ i
  have hy : ∀ j, y j = ∑ i, μ j i • w i := by
    intro j
    have := bV.sum_repr ⟨y j, hyV j⟩
    have := congrArg (fun v : V => (v : K)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hyp : ∀ j, y j ^ p = ∑ i, μ j i ^ p • w i ^ p := by
    intro j
    rw [hy j, sum_pow_char]
    simp only [smul_pow]
  have hsum' : ∑ i, (∑ j, a j * μ j i ^ p) • w i ^ p = 0 := by
    rw [← hsum]
    simp only [hyp, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hcoef : ∀ i, ∑ j, a j * μ j i ^ p = 0 := Fintype.linearIndependent_iff.mp hwp _ hsum'
  have hμ : ∀ j i, μ j i = 0 := by
    intro j i
    have := hind (fun j => μ j i) (by simpa only [mul_comm] using hcoef i)
    exact congrFun this j
  funext j
  rw [Pi.zero_apply, hy j]
  simp only [hμ, zero_smul, Finset.sum_const_zero]

private lemma linearIndepOn_pow_of_PR
  {k : Type u} [Field k]
  (L : Type u) [Field L] [Algebra k L]
  {p : ℕ}
  (t : Finset L)
-- given
  (hp : p.Prime) [ExpChar k p] [CharP L p]
  (h : PR k p L)
  (ht : LinearIndepOn k _root_.id (t : Set L)) :
-- imply
  LinearIndepOn k (· ^ p) (t : Set L) := by
-- proof
  classical
  have : Fact p.Prime := ⟨hp⟩
  unfold LinearIndepOn at ht ⊢
  rw [Fintype.linearIndependent_iff] at ht ⊢
  intro g hg
  let K₀ : Subfield k := (frobenius k p).fieldRange
  let W : Submodule K₀ k := Submodule.span K₀ (Set.range g)
  have : Module.Finite K₀ W := Module.Finite.span_of_finite K₀ (Set.finite_range g)
  let bW := Module.finBasis K₀ W
  let aW : Fin (Module.finrank K₀ W) → k := fun m => (bW m : k)
  have hind : ∀ d : Fin (Module.finrank K₀ W) → k, ∑ m, d m ^ p * aW m = 0 → d = 0 := by
    intro d hd
    have hd' : ∑ m, (⟨d m ^ p, RingHom.mem_fieldRange_self (f := frobenius k p) (d m)⟩ : K₀) • bW m = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul] at hd ⊢
      exact hd
    have := Fintype.linearIndependent_iff.mp bW.linearIndependent _ hd'
    funext m
    apply (pow_eq_zero_iff hp.ne_zero).mp (congrArg Subtype.val (this m))
  have hgW : ∀ x, g x ∈ W := fun x => Submodule.subset_span ⟨x, rfl⟩
  let κ : ↥(t : Set L) → Fin (Module.finrank K₀ W) → K₀ := fun x m => bW.repr ⟨g x, hgW x⟩ m
  have hgexp : ∀ x, g x = ∑ m, (κ x m : k) * aW m := by
    intro x
    have := bW.sum_repr ⟨g x, hgW x⟩
    have := congrArg (fun v : W => (v : k)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hκ : ∀ x m, ∃ e : k, e ^ p = (κ x m : k) := by
    intro x m
    obtain ⟨e, he⟩ := RingHom.mem_fieldRange.mp (κ x m).2
    exact ⟨e, by rw [← he, frobenius_def]⟩
  choose e he using hκ
  have hY : ∑ m, aW m • (∑ x, e x m • (x : L)) ^ p = 0 := by
    rw [← hg]
    simp only [sum_pow_char, smul_pow, Finset.smul_sum, smul_smul, hgexp, Finset.sum_smul, he]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]
  have hzero := h _ aW (fun m => ∑ x, e x m • (x : L)) hind hY
  have he0 : ∀ x m, e x m = 0 := by
    intro x m
    apply ht (fun x => e x m) (congrFun hzero m) x
  intro x
  rw [hgexp x]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← he x m, he0 x m, zero_pow hp.ne_zero, zero_mul]


/--
[Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_linearIndepOn_pow_localization_atPrime_of_mem_minimalPrimes_of_dense.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
  {p : ℕ}
-- given
  (hp : p.Prime) [ExpChar k p]
  {S : Set (PrimeSpectrum B)}
  (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
  (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
    (∀ t : Finset K, LinearIndepOn k _root_.id (t : Set K) → LinearIndepOn k (· ^ p) (t : Set K)) ∧
    Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
  {𝔮 : Ideal B} [𝔮.IsPrime]
  (h𝔮 : 𝔮 ∈ minimalPrimes B)
  {s : Finset (Localization.AtPrime 𝔮)}
  (hs : LinearIndepOn k _root_.id (s : Set (Localization.AtPrime 𝔮))) :
-- imply
  LinearIndepOn k (· ^ p) (s : Set (Localization.AtPrime 𝔮)) := by
-- proof
  classical
  have : CharP k p := by
    obtain h0 | ⟨p', hp', hc⟩ := CharP.exists' k
    ·
      apply absurd (ExpChar.eq (@ExpChar.zero k _ h0) ‹ExpChar k p›) hp.one_lt.ne
    ·
      apply (ExpChar.eq (@ExpChar.prime k _ p' hp'.out hc) ‹ExpChar k p›) ▸ hc
  have hRS : ∀ 𝔰 ∈ S, PR k p 𝔰.asIdeal.ResidueField := by
    intro 𝔰 h𝔰
    obtain ⟨K, iF, iA, hK, ⟨φ⟩⟩ := hsep 𝔰 h𝔰
    let _ := iF
    let _ := iA
    have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    apply PR.of_injective φ φ.toRingHom.injective (PR.of_field K hp hK)
  have hRB : PR k p B := PR.of_dense S hdense hRS
  have hRL : PR k p (Localization.AtPrime 𝔮) := PR.localization hp.pos hRB 𝔮.primeCompl _
  have hrad : ((⊥ : Ideal B).map (algebraMap B (Localization.AtPrime 𝔮))).radical =
      𝔮.map (algebraMap B (Localization.AtPrime 𝔮)) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime 𝔮) 𝔮 ⊥ h𝔮
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← hrad, Ideal.map_bot]
    apply nilradical_eq_zero (Localization.AtPrime 𝔮)
  have hfield : IsField (Localization.AtPrime 𝔮) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  let _ : Field (Localization.AtPrime 𝔮) := hfield.toField
  have : CharP (Localization.AtPrime 𝔮) p :=
    charP_of_injective_algebraMap (algebraMap k (Localization.AtPrime 𝔮)).injective p
  apply linearIndepOn_pow_of_PR (Localization.AtPrime 𝔮) s hp hRL hs


-- created on 2026-10-13
