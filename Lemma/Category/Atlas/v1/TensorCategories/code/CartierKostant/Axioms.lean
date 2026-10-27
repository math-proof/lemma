import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms.Part3
open Coalgebra HopfAlgebra
open scoped TensorProduct


/--
[cocommutative_comul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma cocommutative_comul_apply
  {R : Type u}
  {H : Type v}
  [CommSemiring R]
  [AddCommMonoid H]
  [Module R H]
  [Coalgebra R H]
  [Coalgebra.IsCocommutative R H]
-- given
  (h : H) :
-- imply
  (TensorProduct.comm R H H) (comul (R := R) h) = comul h :=
-- proof
  LinearMap.congr_fun Coalgebra.IsCocommutative.cocomm h
section PrimitiveElements
variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [Bialgebra R H]

/--
[HopfAlgebra.IsPrimitive.algebraMap_counit_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsPrimitive.algebraMap_counit_eq_zero
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [Bialgebra R H]
  {x : H}
-- given
  (hx : HopfAlgebra.IsPrimitive (R := R) x) :
-- imply
  algebraMap R H (Coalgebra.counit (R := R) x) = 0 := by
-- proof
  have h := Coalgebra.rTensor_counit_comul (R := R) x
  rw [hx] at h
  simp only [map_add, LinearMap.rTensor_tmul, Bialgebra.counit_one] at h
  have h2 := congr_arg (TensorProduct.lid R H) h
  simp only [map_add, TensorProduct.lid_tmul, one_smul] at h2
  rw [Algebra.algebraMap_eq_smul_one]
  have : counit (R := R) x • (1 : H) = 0 := by
    have := sub_eq_zero.mpr h2
    simp at this
    exact this
  exact this

/--
[HopfAlgebra.IsPrimitive.commutator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsPrimitive.commutator
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [Bialgebra R H]
  {x y : H}
-- given
  (hx : HopfAlgebra.IsPrimitive (R := R) x)
  (hy : HopfAlgebra.IsPrimitive (R := R) y) :
-- imply
  HopfAlgebra.IsPrimitive (R := R) (x * y - y * x) := by
-- proof
  have := hx.lie_bracket hy
  rwa [Ring.lie_def] at this
end PrimitiveElements
section PrimitiveLieAlgebra
variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/--
[HopfAlgebra.canonicalMapUEA_range_le_adjoin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.canonicalMapUEA_range_le_adjoin
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H] :
-- imply
  (HopfAlgebra.canonicalMapUEA (R := R) (H := H)).range ≤ Algebra.adjoin R (HopfAlgebra.primitiveElements (R := R) (H := H) : Set H) := by
-- proof
  intro x hx
  rw [AlgHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H))) y
  set g := (HopfAlgebra.canonicalMapUEA (R := R) (H := H)).comp
    (UniversalEnvelopingAlgebra.mkAlgHom R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)))
  change g z ∈ _
  induction z using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [g, AlgHom.commutes, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ r
  | ι m =>
    show g (TensorAlgebra.ι R m) ∈ _
    have : g (TensorAlgebra.ι R m) =
      (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl m := by
      simp only [g, AlgHom.comp_apply, HopfAlgebra.canonicalMapUEA]
      exact congr_fun (UniversalEnvelopingAlgebra.ι_comp_lift R
        (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl) m
    rw [this]
    exact Algebra.subset_adjoin m.property
  | mul a b ha hb =>
    show g (a * b) ∈ _; rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb =>
    show g (a + b) ∈ _; rw [map_add]; exact Subalgebra.add_mem _ ha hb

/--
[HopfAlgebra.surjective_canonicalMapUEA_adjoin_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.surjective_canonicalMapUEA_adjoin_top
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
-- given
  (hsurj : Function.Surjective (HopfAlgebra.canonicalMapUEA (R := R) (H := H))) :
-- imply
  Algebra.adjoin R (HopfAlgebra.primitiveElements (R := R) (H := H) : Set H) = ⊤ := by
-- proof
  rw [eq_top_iff]; intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact HopfAlgebra.canonicalMapUEA_range_le_adjoin ⟨y, rfl⟩

/--
[HopfAlgebra.primitiveElements_subset_range_canonicalMapUEA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.primitiveElements_subset_range_canonicalMapUEA
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H] :
-- imply
  (HopfAlgebra.primitiveElements (R := k) (H := H) : Set H) ⊆ ↑(HopfAlgebra.canonicalMapUEA (R := k) (H := H)).range := by
-- proof
  intro x hx
  show x ∈ (HopfAlgebra.canonicalMapUEA (R := k) (H := H)).range
  rw [AlgHom.mem_range]
  exact ⟨UniversalEnvelopingAlgebra.ι k ⟨x, hx⟩, by
    have := congr_fun
      (UniversalEnvelopingAlgebra.ι_comp_lift k
        (HopfAlgebra.primitiveLieSubalgebra (R := k) (H := H)).incl) ⟨x, hx⟩
    simp only [Function.comp_apply, HopfAlgebra.canonicalMapUEA] at this ⊢
    exact this⟩

/--
[HopfAlgebra.surjective_of_primitives_generate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.surjective_of_primitives_generate
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {k : Type u}
  {H : Type v}
  [CommRing k]
  [Ring H]
  [HopfAlgebra k H]
-- given
  (hgen : Algebra.adjoin k ((HopfAlgebra.primitiveElements (R := k) (H := H) : Set H)) = ⊤) :
-- imply
  Function.Surjective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by
-- proof
  rw [← AlgHom.range_eq_top]
  rwa [eq_top_iff, ← hgen]
    HopfAlgebra.primitiveElements_subset_range_canonicalMapUEA
section GrouplikeElements
variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/--
[HopfAlgebra.IsGrouplikeHopf.mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.mul
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {g h : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g)
  (hh : HopfAlgebra.IsGrouplikeHopf (R := R) h) :
-- imply
  HopfAlgebra.IsGrouplikeHopf (R := R) (g * h) := by
-- proof
  constructor
  · rw [Bialgebra.comul_mul, hg.1, hh.1]
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  · rw [Bialgebra.counit_mul, hg.2, hh.2, one_mul]

/--
[HopfAlgebra.IsGrouplikeHopf.one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.one
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H] :
-- imply
  HopfAlgebra.IsGrouplikeHopf (R := R) (1 : H) := by
-- proof
  constructor
  · rw [Bialgebra.comul_one]; simp [Algebra.TensorProduct.one_def]
  · exact Bialgebra.counit_one

/--
[HopfAlgebra.IsGrouplikeHopf.mul_antipode](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.mul_antipode
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
-- imply
  g * antipode R g = 1 := by
-- proof
  have := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) g
  rw [hg.1] at this
  simp [LinearMap.lTensor_tmul, LinearMap.mul'_apply,
    hg.2, Algebra.algebraMap_eq_smul_one] at this
  exact this

/--
[HopfAlgebra.IsGrouplikeHopf.antipode_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.antipode_mul
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
-- imply
  antipode R g * g = 1 := by
-- proof
  have := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) g
  rw [hg.1] at this
  simp [LinearMap.rTensor_tmul, LinearMap.mul'_apply,
    hg.2, Algebra.algebraMap_eq_smul_one] at this
  exact this

/--
[HopfAlgebra.IsGrouplikeHopf.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.ne_zero
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  [Nontrivial R]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
-- imply
  g ≠ 0 := by
-- proof
  intro h
  have h2 := hg.2
  rw [h, map_zero] at h2
  exact zero_ne_one h2

/--
[HopfAlgebra.IsGrouplikeHopf.counit_antipode](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.IsGrouplikeHopf.counit_antipode
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {g : H}
-- given
  (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) :
-- imply
  counit (R := R) (antipode R g) = 1 := by
-- proof
  rwa [HopfAlgebra.counit_antipode]
end GrouplikeElements
/-- Existence of the PBW filtration on `U(Prim(H))` compatible with the coradical
filtration of `H`: there is a monotone, exhaustive filtration `F : ℕ → Submodule k U` such
that `canonicalMapUEA` maps `F n` into the `n`-th piece of the coradical filtration. -/
section SymmetricCocycle
variable (k : Type u) (V : Type u) [Field k] [CharZero k] [AddCommGroup V] [Module k V]

/--
[SymmetricAlgebra.mulMap_comp_comul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma SymmetricAlgebra.mulMap_comp_comul
  {k : Type u}
  {V : Type u}
  [Field k]
  [CharZero k]
  [AddCommGroup V]
  [Module k V] :
-- imply
  (SymmetricAlgebra.mulMap k V).comp (SymmetricAlgebra.comul k V) = SymmetricAlgebra.doubling k V := by
-- proof
  ext v
  show (mulMap k V) ((comul k V) (SymmetricAlgebra.ι k (M := V) v)) =
    (doubling k V) (SymmetricAlgebra.ι k (M := V) v)
  simp only [comul, SymmetricAlgebra.lift_ι_apply, LinearMap.add_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_add]
  rw [show (mulMap k V) (Algebra.TensorProduct.includeLeft (SymmetricAlgebra.ι k (M := V) v)) =
    SymmetricAlgebra.ι k (M := V) v from by simp [mulMap]]
  rw [show (mulMap k V) (Algebra.TensorProduct.includeRight (SymmetricAlgebra.ι k (M := V) v)) =
    SymmetricAlgebra.ι k (M := V) v from by simp [mulMap]]
  simp only [doubling, SymmetricAlgebra.lift_ι_apply, LinearMap.smul_apply]
  ring

/--
[SymmetricAlgebra.mulMap_includeLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma SymmetricAlgebra.mulMap_includeLeft
  {k : Type u}
  {V : Type u}
  [Field k]
  [CharZero k]
  [AddCommGroup V]
  [Module k V]
  {w : SV} :
-- imply
  SymmetricAlgebra.mulMap k V ((Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w) = w := by
-- proof
  simp [SymmetricAlgebra.mulMap]

/--
[SymmetricAlgebra.mulMap_includeRight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma SymmetricAlgebra.mulMap_includeRight
  {k : Type u}
  {V : Type u}
  [Field k]
  [CharZero k]
  [AddCommGroup V]
  [Module k V]
  {w : SV} :
-- imply
  SymmetricAlgebra.mulMap k V ((Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w) = w := by
-- proof
  simp [SymmetricAlgebra.mulMap]

/--
[SymmetricAlgebra.mulMap_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma SymmetricAlgebra.mulMap_coboundary
  {k : Type u}
  {V : Type u}
  [Field k]
  [CharZero k]
  [AddCommGroup V]
  [Module k V]
  {w : SV} :
-- imply
  SymmetricAlgebra.mulMap k V ((SymmetricAlgebra.comul k V) w - (Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w - (Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w) = SymmetricAlgebra.doubling k V w - 2 * w := by
-- proof
  have h1 : (SymmetricAlgebra.mulMap k V) ((SymmetricAlgebra.comul k V) w) =
    (SymmetricAlgebra.doubling k V) w := by
    rw [← AlgHom.comp_apply, SymmetricAlgebra.mulMap_comp_comul]
  simp only [map_sub, h1, SymmetricAlgebra.mulMap_includeLeft,
    SymmetricAlgebra.mulMap_includeRight]
  ring
end SymmetricCocycle
/-- In characteristic zero, every symmetric 2-cocycle on the symmetric coalgebra `S(V)` is
a coboundary. This is the analytic input to the Cartier–Kostant theorem. -/
section NilradicalHopfInfra

/--
[HopfAlgebra.counit_nilpotent_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.counit_nilpotent_eq_zero
  {k : Type u}
  {H : Type v}
  [Field k]
  [CommRing H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : IsNilpotent x) :
-- imply
  Coalgebra.counit (R := k) x = 0 := by
-- proof
  have h : IsNilpotent (Bialgebra.counitAlgHom k H x) := hx.map _
  rwa [isNilpotent_iff_eq_zero] at h

/--
[HopfAlgebra.antipode_isNilpotent_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.antipode_isNilpotent_comm
  {k : Type u}
  {H : Type v}
  [Field k]
  [CommRing H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : IsNilpotent x) :
-- imply
  IsNilpotent (HopfAlgebra.antipode k x) :=
-- proof
  hx.map (HopfAlgebra.antipodeAlgHom (R := k) (A := H))

/--
[HopfAlgebra.nilpotent_mem_counit_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.nilpotent_mem_counit_ker
  {k : Type u}
  {H : Type v}
  [Field k]
  [CommRing H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : IsNilpotent x) :
-- imply
  x ∈ RingHom.ker (Bialgebra.counitAlgHom k H) := by
-- proof
  simp only [RingHom.mem_ker]
  exact HopfAlgebra.counit_nilpotent_eq_zero hx

/--
[HopfAlgebra.comul_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.comul_isNilpotent
  {k : Type u}
  {H : Type v}
  [Field k]
  [CommRing H]
  [HopfAlgebra k H]
  {x : H}
-- given
  (hx : IsNilpotent x) :
-- imply
  IsNilpotent (Coalgebra.comul (R := k) x) :=
-- proof
  hx.map (Bialgebra.comulAlgHom k H)

/--
[HopfAlgebra.nilradical_le_counit_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
lemma HopfAlgebra.nilradical_le_counit_ker
  {k : Type u}
  {H : Type v}
  [Field k]
  [CommRing H]
  [HopfAlgebra k H] :
-- imply
  nilradical H ≤ RingHom.ker (Bialgebra.counitAlgHom k H) := by
-- proof
  intro x hx
  rw [mem_nilradical] at hx
  simp only [RingHom.mem_ker]
  have h : IsNilpotent (Bialgebra.counitAlgHom k H x) := hx.map _
  rwa [isNilpotent_iff_eq_zero] at h
end NilradicalHopfInfra
/-- A finitely generated subcoalgebra of a commutative Hopf algebra is contained in some
finitely generated Hopf subalgebra. -/
section GrouplikeGroup
variable {R : Type u} {H : Type v}
variable [CommRing R] [Ring H] [HopfAlgebra R H]

/--
[HopfAlgebra.IsPrimitive.lie_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean)
-/
@[path]
private lemma lie_bracket_eq
  {R : Type u}
  {H : Type v}
  [CommRing R]
  [Ring H]
  [Bialgebra R H]
  {x y : H}
-- given
  (hx : HopfAlgebra.IsPrimitive (R := R) x)
  (hy : HopfAlgebra.IsPrimitive (R := R) y) :
-- imply
  HopfAlgebra.IsPrimitive (R := R) ⁅x, y⁆ := by
-- proof
  apply HopfAlgebra.IsPrimitive.lie_bracket hx hy


-- created on 2026-10-23
