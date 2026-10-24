import Lemma.Definitions.Def_ModularCurve_ProlongationTuple
import Lemma.Definitions.Def_ModularCurve_NodeDescent
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

namespace ProlongationTuple

variable (R : ProlongationTuple P)

def nodeIntegers (w : Place k (modularFunctionFieldC k N)) : Subring ↥(modularFunctionFieldBar (N * q)) where
  carrier := {f | f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      f ∈ V.toValuationSubring}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun V _ => zero_mem _⟩
  one_mem' := ⟨one_mem _, one_mem _, fun V _ => one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨add_mem hf₁ hg₁, add_mem hf₂ hg₂, fun V hV => add_mem (hf V hV) (hg V hV)⟩
  neg_mem' := by
    rintro f ⟨hf₁, hf₂, hf⟩
    exact ⟨neg_mem hf₁, neg_mem hf₂, fun V hV => neg_mem (hf V hV)⟩
  mul_mem' := by
    rintro f g ⟨hf₁, hf₂, hf⟩ ⟨hg₁, hg₂, hg⟩
    exact ⟨mul_mem hf₁ hg₁, mul_mem hf₂ hg₂, fun V hV => mul_mem (hf V hV) (hg V hV)⟩

theorem mem_nodeIntegers_iff (w : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.nodeIntegers w ↔ f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
      ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        f ∈ V.toValuationSubring :=
  Iff.rfl

theorem mem_integersFst_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w) : f ∈ R.R₁.integers :=
  hf.1

theorem mem_integersSnd_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w) : f ∈ R.R₂.integers :=
  hf.2.1

theorem mem_toValuationSubring_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = w) :
    f ∈ V.toValuationSubring :=
  hf.2.2 V hV

theorem ord_nonneg_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = w) :
    0 ≤ V.ord f :=
  V.ord_nonneg_of_mem (hf.2.2 V hV)

def nodeResidue₁ (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegers w) →+* ↥(modularFunctionFieldC k N) where
  toFun f := R.residue₁ ⟨f, f.2.1⟩
  map_one' := by
    rw [show (⟨((1 : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (1 : ↥(R.nodeIntegers w)).2.1⟩
      : ↥(R.R₁.integers)) = 1 from rfl, map_one]
  map_mul' f g := by
    rw [show (⟨((f * g : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (f * g).2.1⟩
      : ↥(R.R₁.integers)) = ⟨f, f.2.1⟩ * ⟨g, g.2.1⟩ from rfl, map_mul]
  map_zero' := by
    rw [show (⟨((0 : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (0 : ↥(R.nodeIntegers w)).2.1⟩
      : ↥(R.R₁.integers)) = 0 from rfl, map_zero]
  map_add' f g := by
    rw [show (⟨((f + g : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (f + g).2.1⟩
      : ↥(R.R₁.integers)) = ⟨f, f.2.1⟩ + ⟨g, g.2.1⟩ from rfl, map_add]

def nodeResidue₂ (w : Place k (modularFunctionFieldC k N)) :
    ↥(R.nodeIntegers w) →+* ↥(modularFunctionFieldC k N) where
  toFun f := R.residue₂ ⟨f, f.2.2.1⟩
  map_one' := by
    rw [show (⟨((1 : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (1 : ↥(R.nodeIntegers w)).2.2.1⟩
      : ↥(R.R₂.integers)) = 1 from rfl, map_one]
  map_mul' f g := by
    rw [show (⟨((f * g : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (f * g).2.2.1⟩
      : ↥(R.R₂.integers)) = ⟨f, f.2.2.1⟩ * ⟨g, g.2.2.1⟩ from rfl, map_mul]
  map_zero' := by
    rw [show (⟨((0 : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (0 : ↥(R.nodeIntegers w)).2.2.1⟩
      : ↥(R.R₂.integers)) = 0 from rfl, map_zero]
  map_add' f g := by
    rw [show (⟨((f + g : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (f + g).2.2.1⟩
      : ↥(R.R₂.integers)) = ⟨f, f.2.2.1⟩ + ⟨g, g.2.2.1⟩ from rfl, map_add]

@[simp] theorem nodeResidue₁_apply (w : Place k (modularFunctionFieldC k N)) (f : ↥(R.nodeIntegers w)) :
    R.nodeResidue₁ w f = R.residue₁ ⟨f, f.2.1⟩ := rfl

@[simp] theorem nodeResidue₂_apply (w : Place k (modularFunctionFieldC k N)) (f : ↥(R.nodeIntegers w)) :
    R.nodeResidue₂ w f = R.residue₂ ⟨f, f.2.2.1⟩ := rfl

def nodeIntegersOver (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    Subring ↥(modularFunctionFieldBar (N * q)) where
  carrier := {f | f ∈ R.nodeIntegers w ∧
    ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ NodeLocalized.fieldOver (N * q) K}
  zero_mem' := ⟨zero_mem _, by rw [ZeroMemClass.coe_zero]; exact zero_mem _⟩
  one_mem' := ⟨one_mem _, by rw [OneMemClass.coe_one]; exact one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hfK⟩ ⟨hg, hgK⟩
    exact ⟨add_mem hf hg, by rw [AddMemClass.coe_add]; exact add_mem hfK hgK⟩
  neg_mem' := by
    rintro f ⟨hf, hfK⟩
    exact ⟨neg_mem hf, by rw [NegMemClass.coe_neg]; exact neg_mem hfK⟩
  mul_mem' := by
    rintro f g ⟨hf, hfK⟩ ⟨hg, hgK⟩
    exact ⟨mul_mem hf hg, by rw [MulMemClass.coe_mul]; exact mul_mem hfK hgK⟩

theorem mem_nodeIntegersOver_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.nodeIntegersOver K w ↔ f ∈ R.nodeIntegers w ∧
      ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ NodeLocalized.fieldOver (N * q) K :=
  Iff.rfl

theorem nodeIntegersOver_le (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    R.nodeIntegersOver K w ≤ R.nodeIntegers w :=
  fun _ hf => hf.1

theorem algebraMap_mem_nodeIntegers (w : Place k (modularFunctionFieldC k N)) (c : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.nodeIntegers w :=
  ⟨(R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2, (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2,
    fun V _ => V.algebraMap_mem' _⟩

def nodeConst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    ↥(NodeLocalized.coeffSubring A K) →+* ↥(R.nodeIntegersOver K w) where
  toFun c :=
    ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ),
      R.algebraMap_mem_nodeIntegers w ⟨(c : AlgebraicClosure ℚ), c.2.1⟩,
      by
        have hc : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)
              : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
            = CharPReduction.constSeries K.toSubalgebra.toSubring ⟨(c : AlgebraicClosure ℚ), c.2.2⟩ := rfl
        rw [hc]
        exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)⟩
  map_one' := Subtype.ext (by
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((1 : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = _
    rw [OneMemClass.coe_one, map_one]; rfl)
  map_mul' c d := Subtype.ext (by
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((c * d : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = _
    rw [MulMemClass.coe_mul, map_mul]; rfl)
  map_zero' := Subtype.ext (by
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((0 : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = _
    rw [ZeroMemClass.coe_zero, map_zero]; rfl)
  map_add' c d := Subtype.ext (by
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((c + d : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = _
    rw [AddMemClass.coe_add, map_add]; rfl)

@[simp] theorem coe_nodeConst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    (c : ↥(NodeLocalized.coeffSubring A K)) :
    ((R.nodeConst K w c : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := rfl

structure NodeCoordinates [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) where

  x : ↥(R.nodeIntegersOver K w)

  y : ↥(R.nodeIntegersOver K w)
  x_fst : R.nodeResidue₁ w ⟨x, x.2.1⟩ = 0
  x_snd : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x, x.2.1⟩) = 1
  y_snd : R.nodeResidue₂ w ⟨y, y.2.1⟩ = 0
  y_fst : w.ord (R.nodeResidue₁ w ⟨y, y.2.1⟩) = 1

namespace NodeCoordinates

variable {R} [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)

theorem nodeResidue₁_x_mul_y :
    R.nodeResidue₁ w (⟨c.x, c.x.2.1⟩ * ⟨c.y, c.y.2.1⟩) = 0 := by
  rw [map_mul, c.x_fst, zero_mul]

theorem nodeResidue₂_x_mul_y :
    R.nodeResidue₂ w (⟨c.x, c.x.2.1⟩ * ⟨c.y, c.y.2.1⟩) = 0 := by
  rw [map_mul, c.y_snd, mul_zero]

theorem nodeResidue₂_x_ne_zero : R.nodeResidue₂ w ⟨c.x, c.x.2.1⟩ ≠ 0 := by
  intro h
  have h1 := c.x_snd
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem nodeResidue₁_y_ne_zero : R.nodeResidue₁ w ⟨c.y, c.y.2.1⟩ ≠ 0 := by
  intro h
  have h1 := c.y_fst
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

end NodeCoordinates

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
