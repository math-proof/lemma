import Mathlib
import sympy.Basic
import sympy.algebra.direct_limit
open scoped Classical
open MvPolynomial


/--
[Algebra_exists_isDirectLimit_of_finitePresentation](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_isDirectLimit_of_finitePresentation.lean)
-/

private noncomputable def res
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) : MvPolynomial A R →ₐ[R] MvPolynomial ↥s R :=
  aeval fun a => if h : a ∈ s then X ⟨a, h⟩ else 0

private noncomputable def polyExt
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) : MvPolynomial ↥s R →ₐ[R] MvPolynomial A R :=
  MvPolynomial.rename (fun x : ↥s => (x : A))

private noncomputable def ev
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  : MvPolynomial A R →ₐ[R] A := aeval (R := R) id

private def incl
  {A : Type u}
  {s s' : Finset A} (h : s ⊆ s') : ↥s → ↥s' := fun x => ⟨x.1, h x.2⟩

private def Supp
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) (f : MvPolynomial A R) : Prop := polyExt s (res s f) = f

private def Idx (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] : Type u :=
  Subtype fun p : Finset A × Finset (MvPolynomial A R) => ∀ f ∈ p.2, Supp p.1 f ∧ ev f = 0

private instance {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] :
  Preorder (Idx R A) where
  le i j := i.1.1 ⊆ j.1.1 ∧ i.1.2 ⊆ j.1.2
  le_refl i := ⟨subset_rfl, subset_rfl⟩
  le_trans i j k hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩

private instance {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] :
  Nonempty (Idx R A) := ⟨⟨(∅, ∅), by simp⟩⟩

private noncomputable def rel
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (i : Idx R A) : Ideal (MvPolynomial ↥i.1.1 R) := Ideal.span ((res (R := R) i.1.1) '' (i.1.2 : Set (MvPolynomial A R)))

private abbrev Stage {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (i : Idx R A) : Type u :=
  MvPolynomial ↥i.1.1 R ⧸ rel i

private lemma res_ext
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) (g : MvPolynomial ↥s R) : res (R := R) s (polyExt s g) = g := by
  have : (res (R := R) s).comp (polyExt s) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply, polyExt, rename_X, res, aeval_X, dite_eq_left x.2, AlgHom.id_apply]
  exact congrArg (fun f : MvPolynomial ↥s R →ₐ[R] MvPolynomial ↥s R => f g) this

private lemma res_ext_of_subset
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {s s' : Finset A} (h : s ⊆ s') (g : MvPolynomial ↥s R) :
  res (R := R) s' (polyExt s g) = MvPolynomial.rename (incl h) g := by
  have : (res (R := R) s').comp (polyExt s) = MvPolynomial.rename (incl h) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply, polyExt, rename_X, res, aeval_X, dite_eq_left (h x.2), rename_X]
    rfl
  exact congrArg (fun f : MvPolynomial ↥s R →ₐ[R] MvPolynomial ↥s' R => f g) this

private lemma ext_rename_incl
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {s s' : Finset A} (h : s ⊆ s') (g : MvPolynomial ↥s R) :
  polyExt (R := R) s' (MvPolynomial.rename (incl h) g) = polyExt s g := by
  simp only [polyExt, rename_rename]
  rfl

private lemma ev_ext
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) (g : MvPolynomial ↥s R) :
  ev (R := R) (polyExt s g) = aeval (fun x : ↥s => (x : A)) g := by
  simp only [ev, polyExt, aeval_rename]
  rfl

private lemma supp_mono
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {s s' : Finset A} (h : s ⊆ s') {f : MvPolynomial A R} (hf : Supp s f) : Supp s' f := by
  unfold Supp at hf ⊢
  conv_lhs => rw [← hf]
  rw [res_ext_of_subset h, ext_rename_incl, hf]

private lemma supp_ext
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (s : Finset A) (g : MvPolynomial ↥s R) : Supp (R := R) s (polyExt s g) := by
  unfold Supp
  rw [res_ext]

private lemma idx_directed
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  : IsDirected (Idx R A) (· ≤ ·) := by
  constructor
  intro i j
  refine ⟨⟨(i.1.1 ∪ j.1.1, i.1.2 ∪ j.1.2), ?_⟩, ?_, ?_⟩
  ·
    intro f hf
    obtain h | h := Finset.mem_union.mp hf
    · exact ⟨supp_mono Finset.subset_union_left (i.2 f h).1, (i.2 f h).2⟩
    · exact ⟨supp_mono Finset.subset_union_right (j.2 f h).1, (j.2 f h).2⟩
  · exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  · exact ⟨Finset.subset_union_right, Finset.subset_union_right⟩

private lemma stage_fp
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (i : Idx R A) : Algebra.FinitePresentation R (Stage i) := by
  classical
  have : Algebra.FinitePresentation R (MvPolynomial ↥i.1.1 R) := Algebra.FinitePresentation.mvPolynomial R R _
  refine Algebra.FinitePresentation.quotient ?_
  refine ⟨i.1.2.image (res (R := R) i.1.1), ?_⟩
  rw [Finset.coe_image]
  rfl

private lemma rel_le_comap
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {i j : Idx R A} (h : i ≤ j) :
  rel i ≤ (rel j).comap (MvPolynomial.rename (R := R) (incl h.1)) := by
  rw [rel, Ideal.span_le]
  rintro _ ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, ← res_ext_of_subset h.1, (i.2 f hf).1]
  apply Ideal.subset_span
  exact ⟨f, h.2 hf, rfl⟩

private noncomputable def stageHom
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (i j : Idx R A) (h : i ≤ j) : Stage i →ₐ[R] Stage j :=
  Ideal.quotientMapₐ (rel j) (MvPolynomial.rename (incl h.1)) (rel_le_comap h)


private noncomputable def coc
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (i : Idx R A) : Stage i →ₐ[R] A := by
  refine Ideal.Quotient.liftₐ (rel i) (aeval fun x : ↥i.1.1 => (x : A)) ?_
  intro a ha
  rw [rel] at ha
  refine Submodule.span_induction (p := fun a _ => aeval (fun x : ↥i.1.1 => (x : A)) a = 0) ?_ ?_ ?_ ?_ ha
  ·
    rintro _ ⟨f, hf, rfl⟩
    rw [← ev_ext, (i.2 f hf).1]
    exact (i.2 f hf).2
  · simp
  ·
    intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  ·
    intro r a _ ha
    rw [smul_eq_mul, map_mul, ha, mul_zero]

private lemma trans_mk
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {i j : Idx R A} (h : i ≤ j) (g : MvPolynomial ↥i.1.1 R) :
  stageHom i j h (Ideal.Quotient.mk (rel i) g) = Ideal.Quotient.mk (rel j) (MvPolynomial.rename (incl h.1) g) := rfl

private lemma coc_mk
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  (i : Idx R A) (g : MvPolynomial ↥i.1.1 R) :
  coc i (Ideal.Quotient.mk (rel i) g) = aeval (fun x : ↥i.1.1 => (x : A)) g := rfl

private instance {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] :
  DirectedSystem (fun i : Idx R A => Stage i) (fun i j h => ⇑(stageHom i j h)) where
  map_self := by
    intro i x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk]
    have : incl (le_refl i).1 = (id : ↥i.1.1 → ↥i.1.1) := funext fun x => Subtype.ext rfl
    rw [this, rename_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk, trans_mk, trans_mk, rename_rename]
    rfl

private lemma isDirectLimit
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  :
  IsDirectLimit (fun (i j : Idx R A) h => ⇑(stageHom i j h)) fun i => ⇑(coc i) where
  surj := by
    intro a
    let i : Idx R A := ⟨({a}, ∅), by simp⟩
    refine ⟨i, Ideal.Quotient.mk (rel i) (X ⟨a, Finset.mem_singleton_self a⟩), ?_⟩
    rw [coc_mk, aeval_X]
  compatibility := by
    intro i j hij x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk, coc_mk, coc_mk, aeval_rename]
    rfl
  inj := by
    intro i j mi mj hm
    obtain ⟨gi, rfl⟩ := Ideal.Quotient.mk_surjective mi
    obtain ⟨gj, rfl⟩ := Ideal.Quotient.mk_surjective mj
    rw [coc_mk, coc_mk] at hm
    set g : MvPolynomial A R := polyExt i.1.1 gi - polyExt j.1.1 gj with hg
    have hg_ev : ev (R := R) g = 0 := by
      rw [hg, map_sub, ev_ext, ev_ext, hm, sub_self]
    have hsub_i : i.1.1 ⊆ i.1.1 ∪ j.1.1 := Finset.subset_union_left
    have hsub_j : j.1.1 ⊆ i.1.1 ∪ j.1.1 := Finset.subset_union_right
    have hg_supp : Supp (i.1.1 ∪ j.1.1) g := by
      unfold Supp
      rw [hg, map_sub, map_sub, res_ext_of_subset hsub_i, res_ext_of_subset hsub_j, ext_rename_incl, ext_rename_incl]
    let k : Idx R A := ⟨(i.1.1 ∪ j.1.1, insert g (i.1.2 ∪ j.1.2)), by
      intro f hf
      obtain rfl | hf := Finset.mem_insert.mp hf
      · exact ⟨hg_supp, hg_ev⟩
      ·
        obtain h | h := Finset.mem_union.mp hf
        · exact ⟨supp_mono hsub_i (i.2 f h).1, (i.2 f h).2⟩
        · exact ⟨supp_mono hsub_j (j.2 f h).1, (j.2 f h).2⟩⟩
    have hik : i ≤ k := ⟨hsub_i, fun f hf => Finset.mem_insert_of_mem (Finset.mem_union_left _ hf)⟩
    have hjk : j ≤ k := ⟨hsub_j, fun f hf => Finset.mem_insert_of_mem (Finset.mem_union_right _ hf)⟩
    refine ⟨k, hik, hjk, ?_⟩
    rw [trans_mk, trans_mk]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have : MvPolynomial.rename (incl hik.1) gi - MvPolynomial.rename (incl hjk.1) gj = res (R := R) k.1.1 g := by
      rw [hg, map_sub, res_ext_of_subset hsub_i, res_ext_of_subset hsub_j]
    rw [this]
    apply Ideal.subset_span
    exact ⟨g, Finset.mem_insert_self g _, rfl⟩

@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A] :
-- imply
  ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·)) (S : ι → Type u) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, Algebra R (S i)) (_ : ∀ i, Algebra.FinitePresentation R (S i)) (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) (c : ∀ i, S i →ₐ[R] A) (_ : DirectedSystem S fun i j h => ⇑(t i j h)), IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i) := by
-- proof
  classical
    exact ⟨Idx R A, inferInstance, inferInstance, idx_directed, fun i => Stage i, inferInstance, inferInstance,
      fun i => stage_fp i, stageHom, coc, inferInstance, isDirectLimit⟩


-- created on 2026-10-20
