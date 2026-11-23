module

public import Def.ModularCurve_ProlongationTuple
public import Def.ModularCurve_NodeDescent
public import Structure.ModularCurve_NodeLocalizedPlaces

public noncomputable section

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


public theorem mem_nodeIntegers_iff (w : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.nodeIntegers w ↔ f ∈ R.R₁.integers ∧ f ∈ R.R₂.integers ∧
      ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        f ∈ V.toValuationSubring :=
  Iff.rfl


public theorem mem_integersFst_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w) : f ∈ R.R₁.integers :=
  hf.1


public theorem mem_integersSnd_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w) : f ∈ R.R₂.integers :=
  hf.2.1


public theorem mem_toValuationSubring_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = w) :
    f ∈ V.toValuationSubring :=
  hf.2.2 V hV


public theorem ord_nonneg_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.nodeIntegers w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hV : P.reduceFst V = w) :
    0 ≤ V.ord f :=
  V.ord_nonneg_of_mem (hf.2.2 V hV)


@[simp] public theorem nodeResidue₁_apply (w : Place k (modularFunctionFieldC k N)) (f : ↥(R.nodeIntegers w)) :
    R.nodeResidue₁ w f = R.residue₁ ⟨f, f.2.1⟩ := rfl


@[simp] public theorem nodeResidue₂_apply (w : Place k (modularFunctionFieldC k N)) (f : ↥(R.nodeIntegers w)) :
    R.nodeResidue₂ w f = R.residue₂ ⟨f, f.2.2.1⟩ := rfl


public theorem mem_nodeIntegersOver_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.nodeIntegersOver K w ↔ f ∈ R.nodeIntegers w ∧
      ((f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ NodeLocalized.fieldOver (N * q) K :=
  Iff.rfl


public theorem nodeIntegersOver_le (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N)) :
    R.nodeIntegersOver K w ≤ R.nodeIntegers w :=
  fun _ hf => hf.1


public theorem algebraMap_mem_nodeIntegers (w : Place k (modularFunctionFieldC k N)) (c : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.nodeIntegers w :=
  ⟨(R.R₁.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2, (R.R₂.algebraMap_mem_iff (c : AlgebraicClosure ℚ)).mpr c.2,
    fun V _ => V.algebraMap_mem' _⟩


@[simp] public theorem coe_nodeConst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    (c : ↥(NodeLocalized.coeffSubring A K)) :
    ((R.nodeConst K w c : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) := rfl


namespace NodeCoordinates

variable {R} [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)


public theorem nodeResidue₁_x_mul_y :
    R.nodeResidue₁ w (⟨c.x, c.x.2.1⟩ * ⟨c.y, c.y.2.1⟩) = 0 := by
  rw [map_mul, c.x_fst, zero_mul]


public theorem nodeResidue₂_x_mul_y :
    R.nodeResidue₂ w (⟨c.x, c.x.2.1⟩ * ⟨c.y, c.y.2.1⟩) = 0 := by
  rw [map_mul, c.y_snd, mul_zero]


public theorem nodeResidue₂_x_ne_zero : R.nodeResidue₂ w ⟨c.x, c.x.2.1⟩ ≠ 0 := by
  intro h
  have h1 := c.x_snd
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1


public theorem nodeResidue₁_y_ne_zero : R.nodeResidue₁ w ⟨c.y, c.y.2.1⟩ ≠ 0 := by
  intro h
  have h1 := c.y_fst
  rw [h, Place.ord_zero] at h1
  exact zero_ne_one h1

end NodeCoordinates

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
