/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/Chebyshev.lean -/


import Lemma.Nat.PrimeCounting.Chebyshev

open scoped Asymptotics

-- The little-o bridge between `π` and `θ / log`.
example : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x)
    =o[Filter.atTop] (fun x : ℝ => x / Real.log x) :=
  Chebyshev.primeCounting_sub_theta_div_log_isLittleO

-- Forward direction: `θ(x) ~ x` implies `π(x) ~ x / log x`.
example (h : Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x) :=
  Chebyshev.primeCounting_isEquivalent_of_theta_isEquivalent h

-- Reverse direction: `π(x) ~ x / log x` implies `θ(x) ~ x`.
example (h : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x)) :
    Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x :=
  Chebyshev.theta_isEquivalent_of_primeCounting_isEquivalent h

-- The packaged iff API.
example : ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x))
      ↔ (Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :=
  Chebyshev.primeCounting_isEquivalent_iff_theta_isEquivalent
