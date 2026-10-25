import Mathlib

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Polynomial

def autWeight (q : ℕ) (j : ZMod q) : ℕ :=
  if q = 2 then (if j = 0 then 12 else 1)
  else if q = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3
  else if j = 1728 then 2
  else 1

def ssSetTwo : Finset (ZMod 2) := {0}

def ssSetThree : Finset (ZMod 3) := {0}

def ssSetFive : Finset (ZMod 5) := {0}

def ssSetSeven : Finset (ZMod 7) := {1728}

def ssSetEleven : Finset (ZMod 11) := {0, 1728}

def ssSetThirteen : Finset (ZMod 13) := {5}

def ssPolyTwo : Polynomial (ZMod 2) := ∏ a ∈ ssSetTwo, (X - C a)

def ssPolyThree : Polynomial (ZMod 3) := ∏ a ∈ ssSetThree, (X - C a)

def ssPolyFive : Polynomial (ZMod 5) := ∏ a ∈ ssSetFive, (X - C a)

def ssPolySeven : Polynomial (ZMod 7) := ∏ a ∈ ssSetSeven, (X - C a)

def ssPolyEleven : Polynomial (ZMod 11) := ∏ a ∈ ssSetEleven, (X - C a)

def ssPolyThirteen : Polynomial (ZMod 13) := ∏ a ∈ ssSetThirteen, (X - C a)

def ssModelA (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

def ssModelB (q : ℕ) [NeZero q] (j : ZMod q) : ZMod q :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

def affinePointCount (q : ℕ) [NeZero q] (A B : ZMod q) : ℕ :=
  (Finset.univ.filter fun p : ZMod q × ZMod q => p.2 ^ 2 = p.1 ^ 3 + A * p.1 + B).card

end ModularCurve
