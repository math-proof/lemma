import Mathlib

set_option autoImplicit false

open Finset

namespace FLT
namespace DivisorConvolution

def sigma (k n : ℕ) : ℕ := ∑ d ∈ n.divisors, d ^ k


def sigmaConv (k l N : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 N, sigma k i * sigma l (N - i)


def BesgeIdentity (N : ℕ) : Prop :=
  12 * sigmaConv 1 1 N + 6 * N * sigma 1 N = 5 * sigma 3 N + sigma 1 N

def Weight6Identity (N : ℕ) : Prop :=
  240 * sigmaConv 1 3 N + 30 * N * sigma 3 N + sigma 1 N = 21 * sigma 5 N + 10 * sigma 3 N


def Sols (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun x => x.1 * x.2.1 + x.2.2.1 * x.2.2.2 = N)


def euclidStep (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (x.1 - x.2.2.1, x.2.1, x.2.2.1, x.2.1 + x.2.2.2)

def euclidStepInv (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (x.1 + x.2.2.1, x.2.1, x.2.2.1, x.2.2.2 - x.2.1)

end DivisorConvolution

end FLT

open Finset

namespace FLT
namespace DivisorConvolution
namespace BesgeCertificate

def swap₁ (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (x.2.2.1, x.2.2.2, x.1, x.2.1)

def swap₂ (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (x.2.1, x.1, x.2.2.2, x.2.2.1)

end BesgeCertificate

end DivisorConvolution

end FLT
