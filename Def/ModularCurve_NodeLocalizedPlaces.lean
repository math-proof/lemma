module

public import Def.ModularCurve_ProlongationTuple
public import Def.ModularCurve_NodeDescent
public import Structure.ModularCurve_NodeLocalizedPlaces

@[expose] public section

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

namespace NodeCoordinates

variable {R} [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)

end NodeCoordinates

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end

end
