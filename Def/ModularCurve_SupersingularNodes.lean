import Def.ModularCurve_SpecializeModuli

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable {K : Type*} [Field K]

def frobNodePair (q : ℕ) (a : K) :
    Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  (charLGeomPlaceOfPoint K a, charLGeomPlaceOfPoint K (a ^ q))

def frobNodePairEmb (q : ℕ) :
    K ↪ Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  ⟨frobNodePair q, frobNodePair_injective q⟩

def nodePairsOf (q : ℕ) (S : Finset K) :
    Finset (Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :=
  S.map (frobNodePairEmb q)

def jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : K :=
  Classical.choose ((mem_nodePairsOf_iff q S s).mp s.2)

def nodeEquiv (q : ℕ) (S : Finset K) : ↥S ≃ ↥(nodePairsOf q S) where
  toFun a := ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q a.2⟩
  invFun s := ⟨jOfNode q S s, jOfNode_mem q S s⟩
  left_inv a := Subtype.ext (jOfNode_mk q a.2)
  right_inv s := Subtype.ext (frobNodePair_jOfNode q S s)

def widthOf (q : ℕ) (S : Finset K) (e : K → ℕ) : ↥(nodePairsOf q S) → ℕ :=
  fun s => e (jOfNode q S s)

end ModularCurve

end
