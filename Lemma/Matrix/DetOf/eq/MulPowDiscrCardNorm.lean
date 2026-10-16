import Mathlib
import sympy.Basic
open Matrix


private noncomputable def traceDot
  [CommRing R] [CommRing S] [Algebra R S]
  {κ : Type*} [Fintype κ] :
  LinearMap.BilinForm R (κ → S) :=
  LinearMap.mk₂ R (fun x y : κ → S => Algebra.trace R S (∑ i, x i * y i))
    (fun x x' y => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun r x y => by simp only [Pi.smul_apply, smul_mul_assoc]; rw [← Finset.smul_sum, map_smul])
    (fun x y y' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun r x y => by simp only [Pi.smul_apply, mul_smul_comm]; rw [← Finset.smul_sum, map_smul])

private lemma traceDot_apply
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype κ]
  {x y : κ → S} :
-- imply
  traceDot (κ := κ) x y = Algebra.trace R S (∑ i, x i * y i) := by
-- proof
  rfl

private noncomputable def β
  [CommRing R] [CommRing S] [Algebra R S]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (b : Module.Basis ι R S) :
  Module.Basis (ι × κ) R (κ → S) :=
  b.smulTower (Pi.basisFun S κ)

private lemma β_apply
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} {p : ι × κ} :
-- imply
  β b p = Pi.single p.2 (b p.1) := by
-- proof
  ext k
  rw [β, Module.Basis.smulTower_apply, Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  split_ifs
  ·
    simp
  ·
    simp

private lemma sum_single_mul_single
  [CommRing S]
  [Fintype κ] [DecidableEq κ]
  {i j : κ} {s t : S} :
-- imply
  (∑ k, (Pi.single i s : κ → S) k * (Pi.single j t : κ → S) k) = if i = j then s * t else 0 := by
-- proof
  classical
  have : ∀ k, (Pi.single i s : κ → S) k * (Pi.single j t : κ → S) k =
      if k = i then (if i = j then s * t else 0) else 0 := by
    intro k
    if hki : k = i then
      subst hki
      if hij : k = j then
        subst hij
        simp
      else
        simp [hij]
    else
      simp [hki]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_ite_eq' Finset.univ i]
  simp

private lemma toMatrix_traceDot
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} :
-- imply
  LinearMap.BilinForm.toMatrix (β b) (traceDot (κ := κ)) =
    blockDiagonal fun _ : κ => Algebra.traceMatrix R b := by
-- proof
  ext p q
  rw [LinearMap.BilinForm.toMatrix_apply, traceDot_apply, β_apply, β_apply, sum_single_mul_single,
    blockDiagonal_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  if h : p.2 = q.2 then
    simp [h]
  else
    simp [h]

private lemma det_toMatrix_traceDot
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} :
-- imply
  (LinearMap.BilinForm.toMatrix (β b) (traceDot (κ := κ))).det =
    Algebra.discr R b ^ Fintype.card κ := by
-- proof
  rw [toMatrix_traceDot, det_blockDiagonal, Finset.prod_const, Finset.card_univ, Algebra.discr_def]

private noncomputable def mulVecR
  [CommRing R] [CommRing S] [Algebra R S]
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (G : Matrix κ κ S) :
  (κ → S) →ₗ[R] (κ → S) :=
  (toLin' G).restrictScalars R

private lemma mulVecR_apply
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype κ] [DecidableEq κ]
  {G : Matrix κ κ S} {y : κ → S} :
-- imply
  mulVecR (R := R) G y = G *ᵥ y := by
-- proof
  simp [mulVecR]

private lemma det_mulVecR
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} {G : Matrix κ κ S} :
-- imply
  LinearMap.det (mulVecR (R := R) G) = Algebra.norm R G.det := by
-- proof
  let _ : Module.Free R S := Module.Free.of_basis b
  rw [mulVecR, LinearMap.det_restrictScalars, LinearMap.det_toLin']

private lemma toMatrix_compRight_apply
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} {G : Matrix κ κ S} {p q : ι × κ} :
-- imply
  LinearMap.BilinForm.toMatrix (β b) ((traceDot (κ := κ)).compRight (mulVecR (R := R) G)) p q =
    Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2) := by
-- proof
  rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.compRight_apply, traceDot_apply,
    mulVecR_apply, β_apply, β_apply]
  congr 1
  have hG : ∀ k, (G *ᵥ (Pi.single q.2 (b q.1) : κ → S)) k = G k q.2 * b q.1 := by
    intro k
    simp [mulVec, dotProduct, Pi.single_apply]
  simp_rw [hG]
  have : ∀ k, (Pi.single p.2 (b p.1) : κ → S) k * (G k q.2 * b q.1) =
      if k = p.2 then b p.1 * b q.1 * G p.2 q.2 else 0 := by
    intro k
    if hk : k = p.2 then
      subst hk
      simp
      ring
    else
      simp [hk]
  rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_ite_eq' Finset.univ p.2]
  simp

private lemma det_trace_mul_mul_eq
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} {G : Matrix κ κ S} :
-- imply
  (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)).det =
    Algebra.discr R b ^ Fintype.card κ * Algebra.norm R G.det := by
-- proof
  have hM : (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)) =
      LinearMap.BilinForm.toMatrix (β b) ((traceDot (κ := κ)).compRight (mulVecR (R := R) G)) := by
    ext p q
    rw [Matrix.of_apply, toMatrix_compRight_apply]
  rw [hM, LinearMap.BilinForm.toMatrix_compRight, det_mul, det_toMatrix_traceDot,
    LinearMap.det_toMatrix, det_mulVecR (b := b)]


/--
[Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_det_trace_basis_mul_basis_mul_eq_discr_pow_card_mul_norm_det.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {b : Module.Basis ι R S} {G : Matrix κ κ S} :
-- imply
  (Matrix.of fun p q : ι × κ => Algebra.trace R S (b p.1 * b q.1 * G p.2 q.2)).det =
    Algebra.discr R b ^ Fintype.card κ * Algebra.norm R G.det := by
-- proof
  apply det_trace_mul_mul_eq


-- created on 2026-10-13
