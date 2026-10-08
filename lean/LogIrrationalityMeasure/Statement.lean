import Mathlib

namespace LogIrrationalityMeasure

namespace LogExponent

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {r | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

/-- The target statement for the logarithm of a rational number `α`. -/
def LogEventualLowerBound (α : ℚ) : Prop := EventualLowerBound (Real.log α)

def IntegerEventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ (p q : ℤ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

end LogExponent

end LogIrrationalityMeasure
