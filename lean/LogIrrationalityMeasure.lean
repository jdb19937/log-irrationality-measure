import LogIrrationalityMeasure.Main

/-!
# The irrationality measure of the logarithm of a rational number is 2

Main theorems of the repository.  For every positive rational `α ≠ 1`:

* `irrationality_measure_log`: for every real `ν > 2` there is an integer `Q ≥ 2` such that
  `q^(-ν) ≤ |log α - p/q|` for all integers `p, q` with `q ≥ Q`, and the supremum of the set of
  `ν > 0` admitting infinitely many rationals `r` with `0 < |log α - r| < den(r)^(-ν)` equals `2`.
* `irrationality_measure_log_two`: the case `α = 2`.
* `log_not_liouvilleWith`: `¬ LiouvilleWith p (log α)` for every `p > 2`, in Mathlib's vocabulary.

The supremum is `irrationalityExponent`, the definition copied unchanged from OpenAI's
formalization of `μ(π) = 2` (github.com/openai/math, `LogIrrationalityMeasure/Statement.lean`
here).  The proof under `LogIrrationalityMeasure/` is that formalization modified module by
module.  `AxiomCheck.lean` verifies that every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace LogIrrationalityMeasure

open LogIrrationalityMeasure.LogExponent

/-- The irrationality measure of `log α` is `2` for every positive rational `α ≠ 1`:
the explicit lower bound for every `ν > 2`, and the supremum of admissible exponents. -/
theorem irrationality_measure_log (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q →
        (q : ℝ) ^ (-ν) ≤ |Real.log α - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log α - (r : ℝ)| ∧
        |Real.log α - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 :=
  log_main α hα hα1

/-- `μ(log α) = 2`, with the supremum written as `irrationalityExponent`. -/
theorem irrationalityExponent_log (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) :
    irrationalityExponent (Real.log α) = 2 :=
  log_irrationalityExponent α hα hα1

/-- `μ(log 2) = 2`. -/
theorem irrationality_measure_log_two :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q →
        (q : ℝ) ^ (-ν) ≤ |Real.log 2 - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log 2 - (r : ℝ)| ∧
        |Real.log 2 - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  have h := log_main 2 (by norm_num) (by norm_num)
  simpa using h

/-- `log α` is not Liouville of order `p` for any `p > 2` (Mathlib's `LiouvilleWith`). -/
theorem log_not_liouvilleWith (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) {p : ℝ} (hp : 2 < p) :
    ¬ LiouvilleWith p (Real.log α) :=
  LogExponent.log_not_liouvilleWith α hα hα1 hp

end LogIrrationalityMeasure
