import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma span_pow_le_comap
  {𝒪 : Type u} [CommRing 𝒪] (π : 𝒪) {S : Type u} [CommRing S] [Algebra 𝒪 S] (n : ℕ) :
  Ideal.span {π ^ (n + 1)} ≤
    (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}).comap (algebraMap 𝒪 S) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
  apply Ideal.mem_span_singleton_self
/--
[AlgebraicGeometry_exists_tower_baseChange_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_tower_baseChange_of_isPullback.lean)
-/
@[path]
private lemma main
  (𝒪 : Type u) [CommRing 𝒪] (π : 𝒪)
  (X : ℕ → (Scheme : Type (u + 1))) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
  (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
  (G : Type u) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
  (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
  (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
  (S : Type u) [CommRing S] [Algebra 𝒪 S] :
  ∃ (X' : ℕ → (Scheme : Type (u + 1))) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))) (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n)) (q : ∀ n : ℕ, X' n ⟶ X n), (∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (span_pow_le_comap π n))))) ∧
    (∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))) ∧
    (∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n) ∧
    (∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom) ∧
    (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n) ∧
    (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom) := by
  let fS : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})) ⟶
    Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) := fun n =>
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
      (span_pow_le_comap π n)))
  let tO : ∀ n : ℕ, Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))
  let tS : ∀ n : ℕ, Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})) ⟶
    Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))
  have hsq : ∀ n : ℕ, fS n ≫ tO n = tS n ≫ fS (n + 1) := by
    intro n
    simp only [fS, tO, tS, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl
  let X' : ℕ → (Scheme : Type (u + 1)) := fun n => pullback (xb n) (fS n)
  let q : ∀ n : ℕ, X' n ⟶ X n := fun n => pullback.fst (xb n) (fS n)
  let xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})) :=
    fun n => pullback.snd (xb n) (fS n)
  have hq : ∀ n : ℕ, IsPullback (q n) (xb' n) (xb n) (fS n) := fun n => IsPullback.of_hasPullback _ _
  have wxt : ∀ n : ℕ, (q n ≫ xt n) ≫ xb (n + 1) = (xb' n ≫ tS n) ≫ fS (n + 1) := by
    intro n
    rw [Category.assoc, (hcart n).w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc]
  let xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1) := fun n => pullback.lift (q n ≫ xt n) (xb' n ≫ tS n) (wxt n)
  have hq_xt : ∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n := fun n => pullback.lift_fst _ _ _
  have hxt'_snd : ∀ n : ℕ, xt' n ≫ xb' (n + 1) = xb' n ≫ tS n := fun n => pullback.lift_snd _ _ _
  have hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1)) (tS n) := by
    intro n
    have big : IsPullback (q n ≫ xt n) (xb' n) (xb (n + 1)) (fS n ≫ tO n) := (hq n).paste_horiz (hcart n)
    rw [← hq_xt n, hsq n] at big
    apply big.of_right (hxt'_snd n) (hq (n + 1))
  have wa : ∀ (n : ℕ) (g : G), (q n ≫ (a n g).hom) ≫ xb n = xb' n ≫ fS n := by
    intro n g
    rw [Category.assoc, ha_over, pullback.condition]
  let ah : ∀ n : ℕ, G → (X' n ⟶ X' n) := fun n g => pullback.lift (q n ≫ (a n g).hom) (xb' n) (wa n g)
  have ah_fst : ∀ (n : ℕ) (g : G), ah n g ≫ q n = q n ≫ (a n g).hom := fun n g => pullback.lift_fst _ _ _
  have ah_snd : ∀ (n : ℕ) (g : G), ah n g ≫ xb' n = xb' n := fun n g => pullback.lift_snd _ _ _
  have ah_one : ∀ n : ℕ, ah n 1 = 𝟙 _ := by
    intro n
    apply pullback.hom_ext
    ·
      rw [ah_fst, map_one, Category.id_comp]
      apply Category.comp_id
    · rw [ah_snd, Category.id_comp]
  have ah_mul : ∀ (n : ℕ) (g h : G), ah n (g * h) = ah n h ≫ ah n g := by
    intro n g h
    apply pullback.hom_ext
    ·
      rw [ah_fst, Category.assoc, ah_fst, ← Category.assoc, ah_fst, Category.assoc, map_mul]
      rfl
    · rw [ah_snd, Category.assoc, ah_snd, ah_snd]
  let aiso : ∀ n : ℕ, G → Aut (X' n) := fun n g =>
    Iso.mk (ah n g) (ah n g⁻¹) (by rw [← ah_mul, inv_mul_cancel, ah_one])
      (by rw [← ah_mul, mul_inv_cancel, ah_one])
  let a' : ∀ n : ℕ, G →* Aut (X' n) := fun n =>
    { toFun := aiso n,
      map_one' := by
        apply Iso.ext
        apply ah_one n,
      map_mul' := fun g h => by
        apply Iso.ext
        apply ah_mul n g h }
  have ha'hom : ∀ (n : ℕ) (g : G), (a' n g).hom = ah n g := fun n g => rfl
  refine ⟨X', xb', xt', a', q, hq, hcart', hq_xt, ?_, ?_, ?_⟩
  ·
    intro n g
    rw [ha'hom]
    apply ah_fst n g
  ·
    intro n g
    rw [ha'hom]
    apply ah_snd n g
  ·
    intro n g
    rw [ha'hom, ha'hom]
    apply pullback.hom_ext
    ·
      have e1 : (ah n g ≫ xt' n) ≫ q (n + 1) = q n ≫ xt n ≫ (a (n + 1) g).hom := by
        rw [Category.assoc, hq_xt, ← Category.assoc, ah_fst, Category.assoc, ha_xt]
      refine e1.trans ?_
      symm
      rw [Category.assoc, ah_fst, ← Category.assoc, hq_xt, Category.assoc]
    ·
      have e1 : (ah n g ≫ xt' n) ≫ xb' (n + 1) = xb' n ≫ tS n := by
        rw [Category.assoc, hxt'_snd, ← Category.assoc, ah_snd]
      refine e1.trans ?_
      symm
      rw [Category.assoc, ah_snd, hxt'_snd]


-- created on 2026-10-20
