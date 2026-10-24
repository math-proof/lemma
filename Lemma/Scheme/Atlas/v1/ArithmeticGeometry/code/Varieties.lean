import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Varieties


/--
[IsAffineVariety.isAlgebraicSubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma IsAffineVariety.isAlgebraicSubset
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (h : IsAffineVariety k n V) :
-- imply
  IsAlgebraicSubset k n V :=
-- proof
  h.1

/--
[IsAffineVariety.nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma IsAffineVariety.nonempty
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (h : IsAffineVariety k n V) :
-- imply
  V.Nonempty :=
-- proof
  h.2.1

/--
[isClosed_zariskiTopology_iff_isAlgebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma isClosed_zariskiTopology_iff_isAlgebraicSet
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)} :
-- imply
  @IsClosed _ (zariskiTopology k n) V ↔ IsAlgebraicSetAffine k n V := by
-- proof
  constructor
  · intro hV
    have : Vᶜᶜ ∈ algebraicSetsCollection k n := hV.isOpen_compl
    rwa [compl_compl] at this
  · intro hV
    exact @IsClosed.mk _ (zariskiTopology k n) _
      (by show Vᶜᶜ ∈ algebraicSetsCollection k n; rwa [compl_compl])
noncomputable section

variable (k : Type*) [Field k]
/--
[eval_bind₁_eq_eval_polyMapEval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma eval_bind₁_eq_eval_polyMapEval {m n : ℕ} (P : AffineSpace_k k m)
  (f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
  (g : MvPolynomial (Fin n) (AlgebraicClosure k)) :
  MvPolynomial.eval P (MvPolynomial.bind₁ f g) =
  MvPolynomial.eval (polyMapEval k m n f P) g := by
  change MvPolynomial.eval₂Hom _ P (MvPolynomial.bind₁ f g) =
    MvPolynomial.eval₂Hom _ (polyMapEval k m n f P) g
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 1

variable (k : Type*) [Field k]
/--
[polyMapEval_bind₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma polyMapEval_bind₁ {m n r : ℕ} (P : AffineSpace_k k m)
  (f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
  (g : Fin r → MvPolynomial (Fin n) (AlgebraicClosure k)) :
  polyMapEval k m r (fun j => MvPolynomial.bind₁ f (g j)) P =
  polyMapEval k n r g (polyMapEval k m n f P) := by
  ext j
  exact eval_bind₁_eq_eval_polyMapEval k P f (g j)

/--
[AffineMorphism.image_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma AffineMorphism.image_mem
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y}
  {P : AffineSpace_k k m}
-- given
  (hP : P ∈ X) :
-- imply
  φ.toFun k P ∈ Y :=
-- proof
  φ.maps_to P hP

/--
[ratMapDom_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma ratMapDom_subset
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)} :
-- imply
  ratMapDom k m n X denoms ⊆ X :=
-- proof
  fun _ h => h.1

/--
[RationalMap.image_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma RationalMap.image_mem
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : RationalMap k m n X Y}
  {P : AffineSpace_k k m}
-- given
  (hP : P ∈ φ.dom k) :
-- imply
  φ.toFun k P ∈ Y :=
-- proof
  φ.maps_to P hP

/--
[AffineMorphism.toRationalMap_dom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma AffineMorphism.toRationalMap_dom
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y} :
-- imply
  (φ.toRationalMap k).dom k = X := by
-- proof
  simp [RationalMap.dom, AffineMorphism.toRationalMap, ratMapDom_of_denom_one]

/--
[AffineMorphism.toRationalMap_isRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma AffineMorphism.toRationalMap_isRegular
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y} :
-- imply
  (φ.toRationalMap k).IsRegular := by
-- proof
  simp [RationalMap.IsRegular, AffineMorphism.toRationalMap_dom]

/--
[AffineMorphism.toRationalMap_toFun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma AffineMorphism.toRationalMap_toFun_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {f : AffineMorphism k m n X Y}
  {P : AffineSpace_k k m} :
-- imply
  (f.toRationalMap k).toFun k P = f.toFun k P := by
-- proof
  ext j
  simp [RationalMap.toFun, ratMapEval, ratFunEval, AffineMorphism.toRationalMap,
    AffineMorphism.toFun, polyMapEval, map_one, div_one]

/--
[regular_rational_function_is_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma regular_rational_function_is_polynomial
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  {m : ℕ}
  {X : Set (AffineSpace_k k m)}
  {num denom : MvPolynomial (Fin m) (AlgebraicClosure k)}
-- given
  (hX : IsAffineVariety k m X)
  (_hdenom_ne_zero : denom ≠ 0)
  (hdenom_nonvanishing : ∀ P ∈ X, MvPolynomial.eval P denom ≠ 0) :
-- imply
  ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k), ∀ P ∈ X, MvPolynomial.eval P poly = MvPolynomial.eval P num / MvPolynomial.eval P denom := by
-- proof
  set k' := AlgebraicClosure k
  set I := MvPolynomial.vanishingIdeal k' X with hI_def
  have htop : I ⊔ Ideal.span {denom} = ⊤ := by
    by_contra hne_top
    have hrad : (I ⊔ Ideal.span {denom}).radical ≠ ⊤ := by rwa [Ne, Ideal.radical_eq_top]
    rw [← @MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (AlgebraicClosure k) (AlgebraicClosure k) _ _ _ (Fin m) _ _] at hrad
    have hzl_ne : (MvPolynomial.zeroLocus k' (I ⊔ Ideal.span {denom})).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      exact hrad (by rw [hempty, MvPolynomial.vanishingIdeal_empty])
    obtain ⟨P, hP⟩ := hzl_ne
    have hPI : P ∈ MvPolynomial.zeroLocus k' I :=
      MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection.monotone_l le_sup_left hP
    have hPd : P ∈ MvPolynomial.zeroLocus k' (Ideal.span {denom}) :=
      MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection.monotone_l le_sup_right hP
    have hPX : P ∈ X := by
      obtain ⟨S, hS⟩ := hX.1
      rw [hS]
      rw [MvPolynomial.mem_zeroLocus_iff] at hPI
      intro f hf
      have : f ∈ I := by
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro Q hQ
        rw [hS] at hQ
        exact hQ f hf
      exact hPI f this
    have hdenom_zero : MvPolynomial.eval P denom = 0 := by
      rw [MvPolynomial.mem_zeroLocus_iff] at hPd
      rw [eval_eq_aeval_algebraicClosure]
      exact hPd denom (Ideal.subset_span rfl)
    exact hdenom_nonvanishing P hPX hdenom_zero
  have h1 : (1 : MvPolynomial (Fin m) k') ∈ I ⊔ Ideal.span {denom} :=
    htop ▸ Submodule.mem_top
  obtain ⟨h_ix, hh_ix, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨c * num, fun P hP => ?_⟩
  have h_ix_vanish : MvPolynomial.eval P h_ix = 0 := by
    rw [eval_eq_aeval_algebraicClosure]
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hh_ix) P hP
  have hdenom_ne : MvPolynomial.eval P denom ≠ 0 := hdenom_nonvanishing P hP
  have heval : MvPolynomial.eval P denom * MvPolynomial.eval P c = 1 := by
    have hab' := congr_arg (MvPolynomial.eval P) hab
    simp only [map_add, map_mul, map_one] at hab'
    rwa [h_ix_vanish, zero_add] at hab'
  simp only [map_mul]
  rw [eq_div_iff hdenom_ne]
  have heval' : MvPolynomial.eval P c * MvPolynomial.eval P denom = 1 := by
    rw [mul_comm]; exact heval
  rw [mul_assoc, mul_comm (MvPolynomial.eval P num) (MvPolynomial.eval P denom),
    ← mul_assoc, heval', one_mul]

/--
[regular_rational_map_is_morphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
lemma regular_rational_map_is_morphism
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : RationalMap k m n X Y}
-- given
  (hX : IsAffineVariety k m X)
  (hreg : φ.IsRegular) :
-- imply
  ∃ (f : AffineMorphism k m n X Y), ∀ P ∈ X, f.toFun k P = φ.toFun k P := by
-- proof
  have hdenom_nonvanishing : ∀ j, ∀ P ∈ X, MvPolynomial.eval P (φ.denoms j) ≠ 0 := by
    intro j P hP
    have hdom : P ∈ φ.dom k := by rw [show φ.dom k = X from hreg]; exact hP
    exact hdom.2 j
  have hpoly : ∀ j, ∃ poly : MvPolynomial (Fin m) (AlgebraicClosure k),
    ∀ P ∈ X, MvPolynomial.eval P poly =
      MvPolynomial.eval P (φ.nums j) / MvPolynomial.eval P (φ.denoms j) := by
    intro j
    exact regular_rational_function_is_polynomial k hX (φ.nums j) (φ.denoms j)
      (φ.denoms_ne_zero j) (hdenom_nonvanishing j)
  choose polys hpolys using hpoly
  have hpolys_eq : ∀ P ∈ X, polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P := by
    intro P hP
    ext j
    exact hpolys j P hP
  refine ⟨φ.toAffineMorphism k hreg polys hpolys_eq, fun P hP => ?_⟩
  show polyMapEval k m n polys P = ratMapEval k m n φ.nums φ.denoms P
  exact hpolys_eq P hP

/--
[coordinateRingBar_isDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma coordinateRingBar_isDomain_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Set (AffineSpace_k k n)}
-- given
  (hV : IsAffineVariety k n V) :
-- imply
  IsDomain (AffineCoordinateRingBar V) := by
-- proof
  apply coordinateRingBar_isDomain k hV

/--
[algebraicSetsCollection_empty_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma algebraicSetsCollection_empty_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ∅ ∈ algebraicSetsCollection k n := by
-- proof
  apply algebraicSetsCollection_empty_mem k n

/--
[algebraicSetsCollection_sInter_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma algebraicSetsCollection_sInter_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {A : Set (Set (AffineSpace_k k n))}
-- given
  (hA : A ⊆ algebraicSetsCollection k n) :
-- imply
  ⋂₀ A ∈ algebraicSetsCollection k n := by
-- proof
  apply algebraicSetsCollection_sInter_mem k n A hA

/--
[algebraicSetsCollection_union_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma algebraicSetsCollection_union_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {A : Set (AffineSpace_k k n)}
  {B : Set (AffineSpace_k k n)}
-- given
  (hA : A ∈ algebraicSetsCollection k n)
  (hB : B ∈ algebraicSetsCollection k n) :
-- imply
  A ∪ B ∈ algebraicSetsCollection k n := by
-- proof
  apply algebraicSetsCollection_union_mem k n A hA B hB

/--
[eval_bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma eval_bind_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {P : AffineSpace_k k m}
  {f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {g : MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  MvPolynomial.eval P (MvPolynomial.bind₁ f g) = MvPolynomial.eval (polyMapEval k m n f P) g := by
-- proof
  apply eval_bind k P f g

/--
[polyMapEval_bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma polyMapEval_bind_eq
  {k : Type*}
  [Field k]
  {m n r : ℕ}
  {P : AffineSpace_k k m}
  {f : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {g : Fin r → MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  polyMapEval k m r (fun j => MvPolynomial.bind₁ f (g j)) P = polyMapEval k n r g (polyMapEval k m n f P) := by
-- proof
  apply polyMapEval_bind k P f g

/--
[AffineMorphism.toFun_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma toFun_id_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {X : Set (AffineSpace_k k n)}
  {P : AffineSpace_k k n} :
-- imply
  (AffineMorphism.id k X).toFun k P = P := by
-- proof
  apply AffineMorphism.toFun_id k P

/--
[AffineMorphism.toFun_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma toFun_comp_eq
  {k : Type*}
  [Field k]
  {m n r : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {Z : Set (AffineSpace_k k r)}
  {g : AffineMorphism k n r Y Z}
  {f : AffineMorphism k m n X Y}
  {P : AffineSpace_k k m} :
-- imply
  (g.comp k f).toFun k P = g.toFun k (f.toFun k P) := by
-- proof
  apply AffineMorphism.toFun_comp k g f P

/--
[ratMapEval_eq_polyMapEval_of_denom_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma ratMapEval_eq_polyMapEval_of_denom_one_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {P : AffineSpace_k k m} :
-- imply
  ratMapEval k m n polys (fun _ => 1) P = polyMapEval k m n polys P := by
-- proof
  apply ratMapEval_eq_polyMapEval_of_denom_one k polys P

/--
[ratMapDom_of_denom_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean)
-/
@[path]
private lemma ratMapDom_of_denom_one_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)} :
-- imply
  ratMapDom k m n X (fun _ => (1 : MvPolynomial (Fin m) (AlgebraicClosure k))) = X := by
-- proof
  apply ratMapDom_of_denom_one k X


-- created on 2026-10-23
