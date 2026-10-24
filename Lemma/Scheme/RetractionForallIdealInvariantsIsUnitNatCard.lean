import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def osum {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (b : B) : B := ∑ g : G, g • b
private lemma smul_osum {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (h : G) (b : B) : h • osum (O := O) G b = osum (O := O) G b := by
  unfold osum
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  apply Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => rfl)
private lemma osum_add {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (b c : B) : osum (O := O) G (b + c) = osum (O := O) G b + osum (O := O) G c := by
  unfold osum
  rw [← Finset.sum_add_distrib]
  simp_rw [smul_add]
private lemma osum_mul_of_invariant {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (a b : B) (ha : ∀ g : G, g • a = a) : osum (O := O) G (a * b) = a * osum (O := O) G b := by
  unfold osum
  rw [Finset.mul_sum]
  simp_rw [smul_mul', ha]
private lemma osum_of_invariant {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (b : B) (hb : ∀ g : G, g • b = b) : osum (O := O) G b = (Fintype.card G : B) * b := by
  unfold osum
  simp_rw [hb]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
private noncomputable def rey {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (b : B) : B := algebraMap O B u * osum (O := O) G b
private lemma smul_rey {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (h : G) (b : B) : h • rey (O := O) G u b = rey (O := O) G u b := by
  unfold rey
  rw [smul_mul', smul_algebraMap, smul_osum]
private lemma rey_of_invariant {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (hu : u * (Fintype.card G : O) = 1) (b : B) (hb : ∀ g : G, g • b = b) : rey (O := O) G u b = b := by
  unfold rey
  rw [osum_of_invariant (O := O) G b hb, ← mul_assoc, ← map_natCast (algebraMap O B), ← map_mul, hu, map_one, one_mul]
private lemma rey_add {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (b c : B) : rey (O := O) G u (b + c) = rey (O := O) G u b + rey (O := O) G u c := by
  unfold rey
  rw [osum_add, mul_add]
private lemma rey_zero {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) : rey (O := O) G u (0 : B) = 0 := by
  unfold rey osum
  simp
private lemma rey_mul_of_invariant {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (a b : B) (ha : ∀ g : G, g • a = a) : rey (O := O) G u (a * b) = a * rey (O := O) G u b := by
  unfold rey
  rw [osum_mul_of_invariant (O := O) G a b ha]
  ring
private lemma rey_algebraMap_mul {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u r : O) (b : B) : rey (O := O) G u (algebraMap O B r * b) = algebraMap O B r * rey (O := O) G u b :=
  rey_mul_of_invariant (O := O) (B := B) G u (algebraMap O B r) _ (fun g => smul_algebraMap (B := B) g r)
private lemma rey_sub_mem {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G O B] (u : O) (hu : u * (Fintype.card G : O) = 1) (J : Ideal B) (b : B) (hb : ∀ g : G, g • b - b ∈ J) : rey (O := O) G u b - b ∈ J := by
  have h1 : rey (O := O) G u b - b = algebraMap O B u * ∑ g : G, (g • b - b) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_sub, ← mul_assoc, ← map_natCast (algebraMap O B), ← map_mul, hu, map_one, one_mul]
    rfl
  rw [h1]
  apply Ideal.mul_mem_left _ _ (J.sum_mem fun g _ => hb g)
/--
[IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard.lean)
-/
@[path]
private lemma main
  (O A B : Type) [CommRing O] [IsNoetherianRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B] [IsGaloisGroup G A B] [FaithfulSMul A B]
  -- given
  (hG : IsUnit ((Nat.card G : ℕ) : O)) :
  -- imply
  (∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) ∧ (∀ 𝔞 : Ideal O, (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧ (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) → ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B))) ∧ Module.Finite A B ∧ Algebra.FiniteType O A ∧ (Module.Flat O B → Module.Flat O A) := by
  -- proof
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  obtain ⟨u, hu⟩ : ∃ u : O, u * (Fintype.card G : O) = 1 := by
    refine ⟨((hG.unit⁻¹ : Units O) : O), ?_⟩
    rw [← Nat.card_eq_fintype_card]
    apply hG.val_inv_mul
  have hA : ∀ a : A, ∀ g : G, g • algebraMap A B a = algebraMap A B a := fun a g => smul_algebraMap g a
  let toA : B → A := fun b => (IsGaloisGroup.ringEquivFixedPoints G A B).symm ⟨rey (O := O) G u b, fun g => smul_rey (O := O) G u g b⟩
  have htoA : ∀ b : B, algebraMap A B (toA b) = rey (O := O) G u b := fun b => IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply G A B ⟨rey (O := O) G u b, fun g => smul_rey (O := O) G u g b⟩
  have htoA_alg : ∀ a : A, toA (algebraMap A B a) = a := fun a => hinj (by rw [htoA, rey_of_invariant (O := O) G u hu _ (hA a)])
  let r : B →ₗ[A] A := { toFun := toA, map_add' := fun b c => hinj (by rw [map_add, htoA, htoA, htoA, rey_add]), map_smul' := fun a b => hinj (by rw [RingHom.id_apply, htoA, Algebra.smul_def, smul_eq_mul, map_mul, htoA, rey_mul_of_invariant (O := O) G u _ _ (hA a)]) }
  refine ⟨⟨r, htoA_alg⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro 𝔞
    refine ⟨?_, ?_⟩
    ·
      intro a ha
      have key : ∀ x ∈ 𝔞.map (algebraMap O B), ∀ c : B, ∃ a' ∈ 𝔞.map (algebraMap O A), algebraMap A B a' = rey (O := O) G u (c * x) := by
        intro x hx
        refine Submodule.span_induction (p := fun x _ => ∀ c : B, ∃ a' ∈ 𝔞.map (algebraMap O A), algebraMap A B a' = rey (O := O) G u (c * x)) ?_ ?_ ?_ ?_ hx
        ·
          intro y hy c
          obtain ⟨s, hs, rfl⟩ := hy
          refine ⟨algebraMap O A s * toA c, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs), ?_⟩
          rw [map_mul, htoA, ← IsScalarTower.algebraMap_apply, mul_comm c, rey_algebraMap_mul]
        ·
          intro c
          exact ⟨0, Ideal.zero_mem _, by rw [map_zero, mul_zero, rey_zero]⟩
        ·
          intro x y _ _ hx hy c
          obtain ⟨a₁, ha₁, e₁⟩ := hx c
          obtain ⟨a₂, ha₂, e₂⟩ := hy c
          exact ⟨a₁ + a₂, Ideal.add_mem _ ha₁ ha₂, by rw [map_add, e₁, e₂, mul_add, ← rey_add]⟩
        ·
          intro d x _ hx c
          obtain ⟨a₁, ha₁, e₁⟩ := hx (c * d)
          exact ⟨a₁, ha₁, by rw [e₁, smul_eq_mul, mul_assoc]⟩
      obtain ⟨a', ha', e⟩ := key _ ha 1
      rw [one_mul, rey_of_invariant (O := O) G u hu _ (hA a)] at e
      rw [← hinj e]
      apply ha'
    ·
      intro b hb
      refine ⟨toA b, ?_⟩
      rw [htoA]
      apply rey_sub_mem (O := O) G u hu _ b hb
  ·
    let _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
    let _ : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType O A B
    apply Algebra.IsIntegral.finite
  ·
    let _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
    let _ : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType O A B
    let hfin : Module.Finite A B := Algebra.IsIntegral.finite
    exact ⟨fg_of_fg_of_fg O A B Algebra.FiniteType.out (Module.finite_def.mp hfin) hinj⟩
  ·
    intro hflat
    let _ := hflat
    let i : A →ₗ[O] B := (IsScalarTower.toAlgHom O A B).toLinearMap
    let rO : B →ₗ[O] A := r.restrictScalars O
    apply Module.Flat.of_retract i rO
    ext a
    apply htoA_alg a


-- created on 2026-10-20
