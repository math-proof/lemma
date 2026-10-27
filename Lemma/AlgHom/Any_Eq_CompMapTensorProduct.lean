import Mathlib
import Initialize.Tactic.Attr.Basic
open Algebra.TensorProduct MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false


private noncomputable def coord
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T] (i : ι) :
  B ⊗[A] T →ₗ[A] T :=
  TensorProduct.lift
    { toFun := fun b => (β.repr b i) • (LinearMap.id : T →ₗ[A] T)
      map_add' := by
        intro b b'
        ext t
        simp [add_smul]
      map_smul' := by
        intro a b
        ext t
        simp [mul_smul] }

private lemma coord_tmul
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {β : Module.Basis ι A B}
  {T : Type u} [CommRing T] [Algebra A T] (i : ι) (b : B) (t : T) :
-- imply
  coord β i (b ⊗ₜ t) = (β.repr b i) • t := by
-- proof
  simp [coord]

private lemma sum_basis_tmul_coord
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T] (z : B ⊗[A] T) :
-- imply
  ∑ i, β i ⊗ₜ[A] coord β i z = z := by
-- proof
  induction z using TensorProduct.inductionOn with
  | tmul b t =>
    simp only [coord_tmul]
    calc
      _ = ∑ i, (β.repr b i • β i) ⊗ₜ[A] t := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = (∑ i, β.repr b i • β i) ⊗ₜ[A] t := by rw [TensorProduct.sum_tmul]
      _ = b ⊗ₜ t := by rw [β.sum_repr b]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

private lemma coord_sum_basis_tmul
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {β : Module.Basis ι A B}
  {T : Type u} [CommRing T] [Algebra A T] (x : ι → T) (i : ι) :
-- imply
  coord β i (∑ j, β j ⊗ₜ[A] x j) = x i := by
-- proof
  simp [map_sum, coord_tmul, Module.Basis.repr_self, Finsupp.single_apply]

private lemma ext_coord
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T]
  {z z' : B ⊗[A] T}
-- given
  (h : ∀ i, coord β i z = coord β i z') :
-- imply
  z = z' := by
-- proof
  rw [← sum_basis_tmul_coord β z, ← sum_basis_tmul_coord β z']
  simp [h]

private lemma coord_mul
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T] (z z' : B ⊗[A] T) (i : ι) :
-- imply
  coord β i (z * z') = ∑ j, ∑ k, β.repr (β j * β k) i • (coord β j z * coord β k z') := by
-- proof
  conv_lhs => rw [← sum_basis_tmul_coord β z, ← sum_basis_tmul_coord β z']
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]

private lemma coord_smul
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T] (b : B) (z : B ⊗[A] T) (i : ι) :
-- imply
  coord β i (b • z) = ∑ j, β.repr (b * β j) i • coord β j z := by
-- proof
  conv_lhs => rw [← sum_basis_tmul_coord β z]
  rw [Finset.smul_sum]
  simp_rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, coord_tmul]

private lemma coord_one
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T] (i : ι) :
-- imply
  coord β i (1 : B ⊗[A] T) = algebraMap A T (β.repr 1 i) := by
-- proof
  rw [Algebra.TensorProduct.one_def, coord_tmul, Algebra.algebraMap_eq_smul_one]

private lemma coord_map
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {T : Type u} [CommRing T] [Algebra A T]
  {T' : Type u} [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T') (z : B ⊗[A] T) (i : ι) :
-- imply
  coord β i ((map (AlgHom.id B B) u) z) = u (coord β i z) := by
-- proof
  induction z using TensorProduct.inductionOn with
  | tmul b t =>
    simp [map_tmul, coord_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

def IsCoords
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (x : H → ι → T) : Prop :=
  (∀ h h' i, x (h + h') i = x h i + x h' i) ∧
    (∀ (b : B) h i, x (b • h) i = ∑ j, β.repr (b * β j) i • x h j) ∧
    (∀ h h' i, x (h * h') i = ∑ j, ∑ k, β.repr (β j * β k) i • (x h j * x h' k)) ∧
    (∀ i, x 1 i = algebraMap A T (β.repr 1 i))

private lemma isCoords_coord
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (φ : H →ₐ[B] B ⊗[A] T) :
-- imply
  IsCoords β (fun h i => coord β i (φ h)) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro h h' i
    simp [map_add]
  ·
    intro b h i
    dsimp
    rw [map_smul, coord_smul]
  ·
    intro h h' i
    dsimp
    rw [map_mul, coord_mul]
  ·
    intro i
    dsimp
    rw [map_one, coord_one]

private noncomputable def pointOfCoords
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (x : H → ι → T) (hx : IsCoords β x) :
  H →ₐ[B] B ⊗[A] T where
  toFun h := ∑ i, β i ⊗ₜ[A] x h i
  map_one' := by
    apply ext_coord β
    intro i
    rw [coord_sum_basis_tmul, hx.2.2.2, coord_one]
  map_mul' := by
    intro h h'
    apply ext_coord β
    intro i
    rw [coord_sum_basis_tmul, hx.2.2.1, coord_mul]
    simp_rw [coord_sum_basis_tmul]
  map_zero' := by
    have h0 : ∀ i, x 0 i = 0 := by
      intro i
      have := hx.1 0 0 i
      rw [add_zero] at this
      exact left_eq_add.mp this
    simp [h0]
  map_add' := by
    intro h h'
    simp [hx.1, TensorProduct.tmul_add, Finset.sum_add_distrib]
  commutes' := by
    intro b
    apply ext_coord β
    intro i
    rw [coord_sum_basis_tmul, Algebra.algebraMap_eq_smul_one, hx.2.1]
    simp_rw [hx.2.2.2]
    have hb : (b ⊗ₜ[A] (1 : T) : B ⊗[A] T) = b • (1 : B ⊗[A] T) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hb,
      coord_smul]
    simp_rw [coord_one]

private lemma pointOfCoords_apply
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {β : Module.Basis ι A B}
  (x : H → ι → T) (hx : IsCoords β x) (h : H) :
-- imply
  pointOfCoords β x hx h = ∑ i, β i ⊗ₜ[A] x h i :=
  rfl

private lemma coord_pointOfCoords
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {β : Module.Basis ι A B}
  (x : H → ι → T) (hx : IsCoords β x) (h : H) (i : ι) :
-- imply
  coord β i (pointOfCoords β x hx h) = x h i := by
-- proof
  rw [pointOfCoords_apply, coord_sum_basis_tmul]

private lemma pointOfCoords_coord
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (φ : H →ₐ[B] B ⊗[A] T) :
-- imply
  pointOfCoords β (fun h i => coord β i (φ h)) (isCoords_coord β φ) = φ := by
-- proof
  apply AlgHom.ext
  intro h
  rw [pointOfCoords_apply, sum_basis_tmul_coord]

private noncomputable def rels
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  (H : Type u) [CommRing H] [Algebra B H] :
  Set (MvPolynomial (H × ι) A) :=
  {r | (∃ (h h' : H) (i : ι), r = X (h + h', i) - X (h, i) - X (h', i)) ∨
       (∃ (b : B) (h : H) (i : ι), r = X (b • h, i) - ∑ j, C (β.repr (b * β j) i) * X (h, j)) ∨
       (∃ (h h' : H) (i : ι),
         r = X (h * h', i) - ∑ j, ∑ k, C (β.repr (β j * β k) i) * (X (h, j) * X (h', k))) ∨
       (∃ i : ι, r = X ((1 : H), i) - C (β.repr 1 i))}

private noncomputable def relIdeal
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  (H : Type u) [CommRing H] [Algebra B H] :
  Ideal (MvPolynomial (H × ι) A) :=
  Ideal.span (rels β H)

private noncomputable def WR
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  (H : Type u) [CommRing H] [Algebra B H] :
  Type u :=
  MvPolynomial (H × ι) A ⧸ relIdeal β H

noncomputable instance {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B) (H : Type u) [CommRing H] [Algebra B H] : CommRing (WR β H) := inferInstanceAs (CommRing (MvPolynomial (H × ι) A ⧸ relIdeal β H))

noncomputable instance {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B) (H : Type u) [CommRing H] [Algebra B H] : Algebra A (WR β H) := inferInstanceAs (Algebra A (MvPolynomial (H × ι) A ⧸ relIdeal β H))

private lemma forall_aeval_rels_eq_zero_iff
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (x : H → ι → T) :
-- imply
  (∀ r ∈ rels β H, aeval (fun p : H × ι => x p.1 p.2) r = 0) ↔ IsCoords β x := by
-- proof
  constructor
  ·
    intro hr
    refine ⟨fun h h' i => ?_, fun b h i => ?_, fun h h' i => ?_, fun i => ?_⟩
    ·
      have := hr _ (Or.inl ⟨h, h', i, rfl⟩)
      simp only [map_sub, aeval_X] at this
      rwa [sub_sub, sub_eq_zero] at this
    ·
      have := hr _ (Or.inr (Or.inl ⟨b, h, i, rfl⟩))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at this
      rw [sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def _ _).symm
    ·
      have := hr _ (Or.inr (Or.inr (Or.inl ⟨h, h', i, rfl⟩)))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at this
      rw [sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
    ·
      have := hr _ (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
      simp only [map_sub, aeval_X, aeval_C] at this
      rwa [sub_eq_zero] at this
  ·
    intro hx r hr
    cases hr with
    | inl h =>
      obtain ⟨h, h', i, rfl⟩ := h
      simp only [map_sub, aeval_X, hx.1]
      ring
    | inr h =>
      cases h with
      | inl h =>
        obtain ⟨b, h, i, rfl⟩ := h
        rw [map_sub, aeval_X, hx.2.1]
        simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
      | inr h =>
        cases h with
        | inl h =>
          obtain ⟨h, h', i, rfl⟩ := h
          rw [map_sub, aeval_X, hx.2.2.1]
          simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
        | inr h =>
          obtain ⟨i, rfl⟩ := h
          simp only [map_sub, aeval_X, aeval_C, hx.2.2.2, sub_self]

private lemma aeval_mem_relIdeal_eq_zero
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (x : H → ι → T) (hx : IsCoords β x) :
-- imply
  ∀ r ∈ relIdeal β H, aeval (fun p : H × ι => x p.1 p.2) r = 0 := by
-- proof
  intro r hr
  have hle : relIdeal β H ≤ RingHom.ker (aeval (R := A) (fun p : H × ι => x p.1 p.2)) := by
    rw [relIdeal, Ideal.span_le]
    intro r hr
    apply (forall_aeval_rels_eq_zero_iff β x).2 hx r hr
  refine hle hr

private noncomputable def gen
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H] (h : H) (i : ι) :
  WR β H :=
  Ideal.Quotient.mk (relIdeal β H) (X (h, i))

private lemma mkₐ_X
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {β : Module.Basis ι A B}
  {H : Type u} [CommRing H] [Algebra B H] (h : H) (i : ι) :
-- imply
  Ideal.Quotient.mkₐ A (relIdeal β H) (X (h, i)) = gen β h i :=
  rfl

private lemma isCoords_apply_gen
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (f : WR β H →ₐ[A] T) :
-- imply
  IsCoords β (fun h i => f (gen β h i)) := by
-- proof
  rw [← forall_aeval_rels_eq_zero_iff]
  intro r hr
  have hfm : (f.comp (Ideal.Quotient.mkₐ A (relIdeal β H))) =
      aeval (fun p : H × ι => f (gen β p.1 p.2)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [aeval_X]
    rfl
  have hr0 : (Ideal.Quotient.mkₐ A (relIdeal β H) : MvPolynomial (H × ι) A →ₐ[A] WR β H) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)
  rw [← hfm]
  show f ((Ideal.Quotient.mkₐ A (relIdeal β H) : MvPolynomial (H × ι) A →ₐ[A] WR β H) r) = 0
  rw [hr0]
  exact map_zero f

private noncomputable def toPoint
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (f : WR β H →ₐ[A] T) :
  H →ₐ[B] B ⊗[A] T :=
  pointOfCoords β (fun h i => f (gen β h i)) (isCoords_apply_gen β f)

private noncomputable def ofPoint
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  (φ : H →ₐ[B] B ⊗[A] T) :
  WR β H →ₐ[A] T :=
  Ideal.Quotient.liftₐ (relIdeal β H)
    (aeval (fun p : H × ι => (fun (h : H) (i : ι) => coord β i (φ h)) p.1 p.2))
    (aeval_mem_relIdeal_eq_zero β (fun h i => coord β i (φ h)) (isCoords_coord β φ))

private lemma ofPoint_gen
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {β : Module.Basis ι A B}
  (φ : H →ₐ[B] B ⊗[A] T) (h : H) (i : ι) :
-- imply
  ofPoint β φ (gen β h i) = coord β i (φ h) := by
-- proof
  show Ideal.Quotient.lift (relIdeal β H) _ _ (Ideal.Quotient.mk (relIdeal β H) (X (h, i))) = _
  rw [Ideal.Quotient.lift_mk]
  apply aeval_X

private lemma toPoint_apply
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {β : Module.Basis ι A B}
  (f : WR β H →ₐ[A] T) (h : H) :
-- imply
  toPoint β f h = ∑ i, β i ⊗ₜ[A] f (gen β h i) :=
  rfl

private lemma pointOfCoords_congr
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {x x' : H → ι → T} (hx : IsCoords β x) (hx' : IsCoords β x')
-- given
  (e : x = x') :
-- imply
  pointOfCoords β x hx = pointOfCoords β x' hx' := by
-- proof
  subst e
  rfl

private noncomputable def pointsEquiv
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T] :
  (WR β H →ₐ[A] T) ≃ (H →ₐ[B] B ⊗[A] T) where
  toFun := toPoint β
  invFun := ofPoint β
  left_inv := by
    intro f
    refine Ideal.Quotient.algHom_ext A ?_
    apply MvPolynomial.algHom_ext
    intro p
    show ofPoint β (toPoint β f) (Ideal.Quotient.mkₐ A (relIdeal β H) (X p)) =
      f (Ideal.Quotient.mkₐ A (relIdeal β H) (X p))
    rw [mkₐ_X, ofPoint_gen (β := β), toPoint, coord_pointOfCoords]
  right_inv := by
    intro φ
    change pointOfCoords β _ _ = φ
    rw [pointOfCoords_congr β (isCoords_apply_gen β (ofPoint β φ)) (isCoords_coord β φ)
      (funext fun h => funext fun i => ofPoint_gen (β := β) φ h i)]
    apply pointOfCoords_coord β φ

private lemma pointsEquiv_apply
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {β : Module.Basis ι A B}
  (f : WR β H →ₐ[A] T) (h : H) :
-- imply
  pointsEquiv β f h = ∑ i, β i ⊗ₜ[A] f (gen β h i) :=
  rfl

private lemma pointsEquiv_natural
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
  {H : Type u} [CommRing H] [Algebra B H]
  {T : Type u} [CommRing T] [Algebra A T]
  {T' : Type u} [CommRing T'] [Algebra A T']
  (u : T →ₐ[A] T') (f : WR β H →ₐ[A] T) :
-- imply
  pointsEquiv β (u.comp f) = (map (AlgHom.id B B) u).comp (pointsEquiv β f) := by
-- proof
  apply AlgHom.ext
  intro h
  rw [AlgHom.comp_apply, pointsEquiv_apply, pointsEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_tmul]
  rfl


/--
[Algebra_exists_weilRestriction_points_equiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_weilRestriction_points_equiv.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  {H : Type u} [CommRing H] [Algebra B H] :
-- imply
  ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
    ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
      ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T') (f : W →ₐ[A] T),
        e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by
-- proof
  classical
  let ι : Type u := Module.Free.ChooseBasisIndex A B
  let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype A B
  let β : Module.Basis ι A B := Module.Free.chooseBasis A B
  exact ⟨WR β H, inferInstance, inferInstance, fun T _ _ => pointsEquiv β,
    fun T T' _ _ _ _ u f => pointsEquiv_natural β u f⟩


-- created on 2026-10-16
