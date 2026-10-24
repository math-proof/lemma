import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Morphisms
open MvPolynomial AffineParts ProjectiveDimension
open PrimeSpectrum
open AffineParts ProjectiveDimension


/--
[preimage_algebraicSet_of_polyMapEval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
lemma preimage_algebraicSet_of_polyMapEval
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))} :
-- imply
  (polyMapEval k m n polys) ⁻¹' (AlgebraicSet k n S) = AlgebraicSet k m (MvPolynomial.bind₁ polys '' S) := by
-- proof
  ext P
  simp only [Set.mem_preimage, AlgebraicSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h g ⟨f, hfS, hfeq⟩
    rw [← hfeq, eval_bind₁_eq_eval_polyMapEval k P polys f]
    exact h f hfS
  · intro h g hgS
    have := h (MvPolynomial.bind₁ polys g) ⟨g, hgS, rfl⟩
    rwa [eval_bind₁_eq_eval_polyMapEval k P polys g] at this

/--
[affineMorphism_preimage_algebraicSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
lemma affineMorphism_preimage_algebraicSet
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y}
  {Z : Set (AffineSpace_k k n)}
-- given
  (hZ : IsAlgebraicSetAffine k n Z) :
-- imply
  IsAlgebraicSetAffine k m ((φ.toFun k) ⁻¹' Z) := by
-- proof
  obtain ⟨S, rfl⟩ := hZ
  exact ⟨MvPolynomial.bind₁ φ.polys '' S,
    preimage_algebraicSet_of_polyMapEval k φ.polys S⟩

/--
[affineMorphism_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
lemma affineMorphism_continuous
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y} :
-- imply
  @Continuous _ _ (zariskiTopology k m) (zariskiTopology k n) (φ.toFun k) := by
-- proof
  rw [@continuous_def _ _ (zariskiTopology k m) (zariskiTopology k n)]
  intro U hU
  have hUc_closed : @IsClosed _ (zariskiTopology k n) Uᶜ :=
    @IsOpen.isClosed_compl _ (zariskiTopology k n) U hU
  rw [isClosed_zariskiTopology_iff_isAlgebraicSet k n] at hUc_closed
  have hpre : IsAlgebraicSetAffine k m ((φ.toFun k) ⁻¹' Uᶜ) :=
    affineMorphism_preimage_algebraicSet k φ Uᶜ hUc_closed
  rw [Set.preimage_compl] at hpre
  have hpre_closed : @IsClosed _ (zariskiTopology k m) ((φ.toFun k) ⁻¹' U)ᶜ :=
    (isClosed_zariskiTopology_iff_isAlgebraicSet k m _).mpr hpre
  rw [← compl_compl (φ.toFun k ⁻¹' U)]
  exact @IsClosed.isOpen_compl _ (zariskiTopology k m) _ hpre_closed

/--
[affinePartZeroLocus_isAlgebraicSubset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
lemma affinePartZeroLocus_isAlgebraicSubset
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  {n : ℕ}
  {S : Set (MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))}
  {i : Fin (n + 1)} :
-- imply
  IsAlgebraicSubset k n (affinePartZeroLocus (AlgebraicClosure k) S i) := by
-- proof
  refine ⟨{g | ∃ f ∈ S, ∃ d, f.IsHomogeneous d ∧ g = dehomogenize (AlgebraicClosure k) i f}, ?_⟩
  ext a
  simp only [AlgebraicSet, affinePartZeroLocus, Set.mem_setOf_eq]
  constructor
  · intro ha g ⟨f, hfS, d, hfhom, hgdef⟩
    subst hgdef
    exact ha f hfS d hfhom
  · intro ha f hfS d hfhom
    exact ha (dehomogenize (AlgebraicClosure k) i f) ⟨f, hfS, d, hfhom, rfl⟩

/--
[coordRing_iso_induces_variety_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
lemma coordRing_iso_induces_variety_iso
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  {n m : ℕ}
  {X : Set (AffineSpace_k k n)}
  {Y : Set (AffineSpace_k k m)}
  {θ : AffineCoordinateRingBar X ≃+* AffineCoordinateRingBar Y}
-- given
  (hX : IsAlgebraicSubset k n X)
  (hY : IsAlgebraicSubset k m Y)
  (hθ : IsAlgHomBar k θ.toRingHom)
  (hθ_symm : IsAlgHomBar k θ.symm.toRingHom) :
-- imply
  AreIsomorphic k X Y := by
-- proof
  have hX_eq : X = AlgebraicSet k n (idealOfAlgebraicSet X : Set _) :=
    (algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hX).symm
  have hY_eq : Y = AlgebraicSet k m (idealOfAlgebraicSet Y : Set _) :=
    (algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY).symm
  set equiv_XY := corollary_14_9_categorical_equiv k hY_eq (X := X) (Y := Y)
  set equiv_YX := corollary_14_9_categorical_equiv k hX_eq (X := Y) (Y := X)
  set φ_fwd := equiv_XY.varietyFunctor hθ_symm
  set φ_inv := equiv_YX.varietyFunctor hθ
  have left_inv_on_Y : ∀ Q ∈ Y, φ_fwd.toFun k (φ_inv.toFun k Q) = Q := by
    intro Q hQ
    have hP_mem : φ_inv.toFun k Q ∈ X := φ_inv.maps_to Q hQ
    set P := φ_inv.toFun k Q with hP_def
    funext j
    have hRT_XY := equiv_XY.roundTrip_algHom θ.symm.toRingHom hθ_symm
      (MvPolynomial.X j) P hP_mem
    obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective
      (θ.symm.toRingHom (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    have hRT_YX := equiv_YX.roundTrip_algHom θ.toRingHom hθ h Q hQ
    have lhs_XY : evalOnCoordRing k X P hP_mem
      ((equiv_XY.coordRingFunctor (equiv_XY.varietyFunctor hθ_symm))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) =
      φ_fwd.toFun k P j := by
      change evalOnCoordRing k X P hP_mem
        (φ_fwd.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) = _
      rw [AffineMorphism.pullback_eval]
      simp [evalOnCoordRing_mk, MvPolynomial.eval_X]
    have rhs_XY : evalOnCoordRing k X P hP_mem
      (θ.symm.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) =
      MvPolynomial.eval P h := by
      rw [← hh]
      simp [evalOnCoordRing_mk]
    have step1 : φ_fwd.toFun k P j = MvPolynomial.eval P h := by
      rw [← lhs_XY, hRT_XY, rhs_XY]
    have lhs_YX : evalOnCoordRing k Y Q hQ
      ((equiv_YX.coordRingFunctor (equiv_YX.varietyFunctor hθ))
        (Ideal.Quotient.mk (idealOfAlgebraicSet X) h)) =
      MvPolynomial.eval P h := by
      change evalOnCoordRing k Y Q hQ
        (φ_inv.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet X) h)) = _
      rw [AffineMorphism.pullback_eval]
      simp only [evalOnCoordRing_mk]
      rfl
    have rhs_YX : evalOnCoordRing k Y Q hQ
      (θ.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet X) h)) =
      Q j := by
      rw [hh]
      show evalOnCoordRing k Y Q hQ
        (θ.toRingHom (θ.symm.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))) = Q j
      have : θ.toRingHom (θ.symm.toRingHom
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) =
        Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j) := by
        simp
      rw [this]
      simp [evalOnCoordRing_mk, MvPolynomial.eval_X]
    have step2 : MvPolynomial.eval P h = Q j := by
      rw [← lhs_YX, hRT_YX, rhs_YX]
    rw [step1, step2]
  have right_inv_on_X : ∀ P ∈ X, φ_inv.toFun k (φ_fwd.toFun k P) = P := by
    intro P hP
    have hQ_mem : φ_fwd.toFun k P ∈ Y := φ_fwd.maps_to P hP
    set Q := φ_fwd.toFun k P with hQ_def
    funext i
    obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective
      (θ.toRingHom (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    have hRT_YX := equiv_YX.roundTrip_algHom θ.toRingHom hθ
      (MvPolynomial.X i) Q hQ_mem
    have hRT_XY := equiv_XY.roundTrip_algHom θ.symm.toRingHom hθ_symm h P hP
    have lhs_YX : evalOnCoordRing k Y Q hQ_mem
      ((equiv_YX.coordRingFunctor (equiv_YX.varietyFunctor hθ))
        (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i))) =
      φ_inv.toFun k Q i := by
      change evalOnCoordRing k Y Q hQ_mem
        (φ_inv.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i))) = _
      rw [AffineMorphism.pullback_eval]
      simp [evalOnCoordRing_mk, MvPolynomial.eval_X]
    have rhs_YX : evalOnCoordRing k Y Q hQ_mem
      (θ.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i))) =
      MvPolynomial.eval Q h := by
      rw [← hh]
      simp [evalOnCoordRing_mk]
    have step1 : φ_inv.toFun k Q i = MvPolynomial.eval Q h := by
      rw [← lhs_YX, hRT_YX, rhs_YX]
    have lhs_XY : evalOnCoordRing k X P hP
      ((equiv_XY.coordRingFunctor (equiv_XY.varietyFunctor hθ_symm))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) h)) =
      MvPolynomial.eval Q h := by
      change evalOnCoordRing k X P hP
        (φ_fwd.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) h)) = _
      rw [AffineMorphism.pullback_eval]
      simp only [evalOnCoordRing_mk]
      rfl
    have rhs_XY : evalOnCoordRing k X P hP
      (θ.symm.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet Y) h)) =
      P i := by
      rw [hh]
      show evalOnCoordRing k X P hP
        (θ.symm.toRingHom (θ.toRingHom (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i)))) = P i
      have : θ.symm.toRingHom (θ.toRingHom
        (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i))) =
        Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.X i) := by
        simp
      rw [this]
      simp [evalOnCoordRing_mk, MvPolynomial.eval_X]
    have step2 : MvPolynomial.eval Q h = P i := by
      rw [← lhs_XY, hRT_XY, rhs_XY]
    rw [step1, step2]
  exact ⟨⟨φ_fwd, φ_inv, left_inv_on_Y, right_inv_on_X⟩⟩

variable (k : Type*) [Field k]
variable [Field k]
/--
[bind₁_mem_idealOverK_of_maps_to](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
pullback along it sends the $k$-vanishing ideal of $Y$ into that of $X$:
$f \in I_k(Y) \Rightarrow f \circ \mathrm{polys}_K \in I_k(X)$. -/
lemma bind₁_mem_idealOverK_of_maps_to {m n : ℕ}
  {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
  (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
  (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
  (polysK : Fin n → MvPolynomial (Fin m) k)
  (hpolysK : ∀ j, polys j = MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (polysK j))
  {f : MvPolynomial (Fin n) k}
  (hf : f ∈ idealOverK Y) :
  (MvPolynomial.bind₁ polysK) f ∈ idealOverK X := by
  rw [mem_idealOverK_iff] at hf ⊢
  rw [MvPolynomial.map_bind₁]
  have h_eq : (fun i => MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (polysK i)) = polys :=
    funext (fun j => (hpolysK j).symm)
  rw [h_eq]
  exact bind₁_mem_idealOfAlgebraicSet_of_maps_to k polys hmaps hf

/--
[homog_eval_rescale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma homog_eval_rescale_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {f : HomogPoly k n}
  {c : AlgebraicClosure k}
  {v : Fin (n + 1) → AlgebraicClosure k} :
-- imply
  eval (fun i => c * v i) f.poly = c ^ f.deg * eval v f.poly := by
-- proof
  apply homog_eval_rescale k n f c v

/--
[projAlgSets_empty_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma projAlgSets_empty_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ∅ ∈ projAlgSetsCollection k n := by
-- proof
  apply projAlgSets_empty_mem k n

/--
[projAlgSets_sInter_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma projAlgSets_sInter_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {A : Set (Set (ProjectiveSpace_k k n))}
-- given
  (hA : A ⊆ projAlgSetsCollection k n) :
-- imply
  ⋂₀ A ∈ projAlgSetsCollection k n := by
-- proof
  apply projAlgSets_sInter_mem k n A hA

/--
[projAlgSets_union_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma projAlgSets_union_mem_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {A : Set (ProjectiveSpace_k k n)}
  {B : Set (ProjectiveSpace_k k n)}
-- given
  (hA : A ∈ projAlgSetsCollection k n)
  (hB : B ∈ projAlgSetsCollection k n) :
-- imply
  A ∪ B ∈ projAlgSetsCollection k n := by
-- proof
  apply projAlgSets_union_mem k n A hA B hB

/--
[pullback_of_induced_morphism_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma pullback_of_induced_morphism_eq_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
-- given
  (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
  (hθ_alg : ∀ r : AlgebraicClosure k, θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) = Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
  (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
  (heval : ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k)) (P : AffineSpace_k k m) (hP : P ∈ X), evalOnCoordRing k X P hP (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) = MvPolynomial.eval (polyMapEval k m n polys P) g) :
-- imply
  ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k)) (P : AffineSpace_k k m) (hP : P ∈ X), evalOnCoordRing k X P hP ((AffineMorphism.mk polys hmaps).pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) = evalOnCoordRing k X P hP (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) := by
-- proof
  apply pullback_of_induced_morphism_eq k hY θ hθ_alg polys hmaps heval

/--
[induced_morphism_of_pullback_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma induced_morphism_of_pullback_eq_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y}
  {polys' : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
-- given
  (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
  (hφ_alg : ∀ r : AlgebraicClosure k, φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) = Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
  (hmaps' : ∀ P ∈ X, polyMapEval k m n polys' P ∈ Y)
  (heval' : ∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k)) (P : AffineSpace_k k m) (hP : P ∈ X), evalOnCoordRing k X P hP (φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) = MvPolynomial.eval (polyMapEval k m n polys' P) g) :
-- imply
  ∀ (P : AffineSpace_k k m) (hP : P ∈ X), polyMapEval k m n polys' P = φ.toFun k P := by
-- proof
  apply induced_morphism_of_pullback_eq k hY φ hφ_alg polys' hmaps' heval'

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean)
-/
@[path]
private lemma bind_eq
  {k : Type*}
  [Field k]
  {k : Type*}
  [Field k]
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {polysK : Fin n → MvPolynomial (Fin m) k}
  {f : MvPolynomial (Fin n) k}
-- given
  (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
  (hpolysK : ∀ j, polys j = MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (polysK j))
  (hf : f ∈ idealOverK Y) :
-- imply
  (MvPolynomial.bind₁ polysK) f ∈ idealOverK X := by
-- proof
  apply bind k k polys hmaps polysK hpolysK hf


-- created on 2026-10-23
