import Mathlib
import Def.TateCurve_Defect
import Def.NumberTheory_DivisorConvolution
import Theorems.Thm_TateCurve_defectCoeff_one

set_option autoImplicit false

open scoped NNReal


open scoped NNReal

namespace TateCurve

section InteriorConvolution

variable {K : Type*} [NontriviallyNormedField K]

noncomputable def cauchyMulInt (c d : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * d (N - i)


noncomputable def cauchyMulInt3 (c : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * cauchyMulInt c c (N - i)

end InteriorConvolution

end TateCurve

open scoped NNReal

namespace TateCurve

section FGBasis

variable {K : Type*} [Field K] (u : K)

noncomputable def Fz (a : ℤ) : K := u ^ a + u ^ (-a) - 2

noncomputable def Gz (a : ℤ) : K := u ^ a - u ^ (-a)

end FGBasis


def boundaryWeight (d j : ℕ) : ℕ := d * (d - j) ^ 2 * (2 * d - j) / 2


section BoundaryTerm

variable {K : Type*} [NontriviallyNormedField K] {u : K}

noncomputable def boundaryTerm (u : K) (d : ℕ) : K :=
  (2 * yfun u + xfun u) * yDivTerm u d + (yfun u - 3 * xfun u ^ 2) * xDivTerm u d
    + ((5 * d ^ 3 : ℕ) : K) * xfun u + ((b d : ℕ) : K)

end BoundaryTerm

end TateCurve

open scoped NNReal

namespace TateCurve

section Tent

variable {K : Type*} [NontriviallyNormedField K] {u : K}

noncomputable def tent (u : K) (m : ℕ) : K :=
  u * (∑ i ∈ Finset.range m, u ^ i) ^ 2 * (u ^ m)⁻¹

end Tent

end TateCurve

open Finset


open Finset


open Finset

namespace TateCurve

open FLT.DivisorConvolution

section Sols3

def Sols3 (N : ℕ) : Finset ((ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ
      (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)).filter
    (fun y => y.1.1 * y.1.2 + (y.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.2) = N)

end Sols3

end TateCurve

open Finset

namespace TateCurve

open FLT.DivisorConvolution

section LineDefs

def boundaryLine (N k : ℕ) : ℤ :=
  ∑ d ∈ N.divisors.filter (fun d => k < d), (boundaryWeight d k : ℤ)

def mixedLine (N k : ℕ) : ℤ :=
  (∑ x ∈ (Sols N).filter (fun x => x.1 + x.2.2.1 = k),
      ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 - (x.1 : ℤ) * (x.2.2.1 : ℤ)))
    - (∑ x ∈ (Sols N).filter (fun x => ((x.1 : ℤ) - (x.2.2.1 : ℤ)).natAbs = k),
        ((x.1 : ℤ) ^ 2 * (x.2.2.1 : ℤ) ^ 2 + (x.1 : ℤ) * (x.2.2.1 : ℤ)))
    + (∑ x ∈ (Sols N).filter (fun x => x.1 = k), 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ)))
    + (∑ x ∈ (Sols N).filter (fun x => x.2.2.1 = k), 2 * ((x.1 : ℤ) * (x.2.2.1 : ℤ)))

def tentWeight (a c k : ℕ) : ℤ :=
  (a : ℤ) * (c : ℤ) *
    (((a + c - k : ℕ) : ℤ) + ((((a : ℤ) - (c : ℤ)).natAbs - k : ℕ) : ℤ)
      - 2 * ((a - k : ℕ) : ℤ) - 2 * ((c - k : ℕ) : ℤ))

def tentLine (N k : ℕ) : ℤ := ∑ x ∈ Sols N, tentWeight x.1 x.2.2.1 k

def sFiveLine (N k : ℕ) : ℤ :=
  ∑ x ∈ (Sols N).filter (fun x => x.2.2.1 = k), 5 * (x.1 : ℤ) ^ 3 * (x.2.2.1 : ℤ)

def tripleLine (N k : ℕ) : ℤ :=
  (∑ y ∈ (Sols3 N).filter
      (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
      ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ))).natAbs = k),
        ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.2.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.2.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + (y.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - (y.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) + (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    - (∑ y ∈ (Sols3 N).filter
        (fun y => ((y.1.1 : ℤ) - (y.2.2.2.1 : ℤ)).natAbs = k),
        2 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.1.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))
    + (∑ y ∈ (Sols3 N).filter (fun y => ((y.2.2.2.1 : ℤ)).natAbs = k),
        4 * ((y.1.1 : ℤ) * (y.2.1 : ℤ) * (y.2.2.2.1 : ℤ)))

def lineCoeff (N k : ℕ) : ℤ :=
  -4 * boundaryLine N k + mixedLine N k - 12 * tentLine N k + 4 * sFiveLine N k
    - 4 * tripleLine N k

end LineDefs

end TateCurve
