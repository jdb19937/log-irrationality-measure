import LogIrrationalityMeasure.Approximation.AdmissibleMatrixGeometry
import LogIrrationalityMeasure.Approximation.InterpolationConsequence
import LogIrrationalityMeasure.MathlibStatements

/-!
# The irrationality exponent of `log α`

The geometric interpolation theorem `AdmissibleMatrixInterpolation.globalInterpolation`
discharges the hypothesis of the stage-1 conditional theorems, so the exponent statements for
`Real.log α` (`α` a positive rational, `α ≠ 1`) hold unconditionally.
-/

namespace LogIrrationalityMeasure

namespace LogExponent

theorem globalInterpolation (α : ℚ) : DeterminantContradiction.GlobalInterpolationStatement α :=
  AdmissibleMatrixInterpolation.globalInterpolation

theorem log_eventualLowerBound (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) : LogEventualLowerBound α :=
  logEventualLowerBound_of_globalInterpolation α hα hα1 (globalInterpolation α)

theorem log_integerEventualLowerBound (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) :
    IntegerEventualLowerBound (Real.log α) :=
  log_integerEventualLowerBound_of_globalInterpolation α hα hα1 (globalInterpolation α)

theorem log_irrationalityExponent (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) :
    irrationalityExponent (Real.log α) = 2 :=
  log_irrationalityExponent_of_globalInterpolation α hα hα1 (globalInterpolation α)

theorem log_two_irrationalityExponent : irrationalityExponent (Real.log 2) = 2 :=
  log_two_irrationalityExponent_of_globalInterpolation (globalInterpolation 2)

/-- The statement in the shape of the OpenAI challenge file for `π`, for `log α`. -/
theorem log_main (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q →
        (q : ℝ) ^ (-ν) ≤ |Real.log α - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log α - (r : ℝ)| ∧
        |Real.log α - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 :=
  log_main_of_globalInterpolation α hα hα1 (globalInterpolation α)

theorem log_not_liouvilleWith (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1) {p : ℝ} (hp : 2 < p) :
    ¬ LiouvilleWith p (Real.log α) :=
  log_not_liouvilleWith_of_globalInterpolation α hα hα1 (globalInterpolation α) hp

end LogExponent

end LogIrrationalityMeasure
