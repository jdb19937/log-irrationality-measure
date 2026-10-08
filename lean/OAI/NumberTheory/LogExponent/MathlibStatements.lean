import OAI.NumberTheory.LogExponent.Approximation.InterpolationConsequence

/-!
# Audit-facing statements in Mathlib vocabulary

`irrationalityExponent` is the definition vendored from the OpenAI development
(`Statement.lean`): the supremum of the exponents `ν > 0` for which infinitely many
rationals `r` with `r.den ≥ 2` satisfy `0 < |x - r| < r.den ^ (-ν)`.  The statements
below unfold it, so that every theorem here mentions only `Real.log`, casts, `rpow`,
`abs`, `Set.Infinite`, `sSup`, and Mathlib's `LiouvilleWith`.

All results are conditional on `GlobalInterpolationStatement α`, the matrix form of the
separated-weight interpolation theorem for centres `(α^j, j p_i/q_i)`.
-/

namespace OAI

namespace LogExponent

open Filter Real

/-- The statement in the shape of the OpenAI challenge file for `π`, for `log α`. -/
theorem log_main_of_globalInterpolation (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1)
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement α) :
    (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
      ∀ p q : ℤ, Q ≤ q →
        (q : ℝ) ^ (-ν) ≤ |Real.log α - (p : ℝ) / (q : ℝ)|) ∧
    sSup {ν : ℝ | 0 < ν ∧
      Set.Infinite {r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log α - (r : ℝ)| ∧
        |Real.log α - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  refine ⟨log_integerEventualLowerBound_of_globalInterpolation α hα hα1 hgeometry, ?_⟩
  change irrationalityExponent (Real.log α) = 2
  exact log_irrationalityExponent_of_globalInterpolation α hα hα1 hgeometry

/-- An eventual lower bound with exponent `ν'` rules out `LiouvilleWith p` for every `p > ν'`. -/
theorem not_liouvilleWith_of_eventualLowerBound {x : ℝ} (hx : EventualLowerBound x)
    {p : ℝ} (hp : 2 < p) : ¬ LiouvilleWith p x := by
  rintro ⟨C, hC⟩
  set ν' : ℝ := (2 + p) / 2 with hν'
  have h2ν' : 2 < ν' := by rw [hν']; linarith
  have hν'p : 0 < p - ν' := by rw [hν']; linarith
  obtain ⟨Q, -, hQ⟩ := hx ν' h2ν'
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (p - ν')) atTop atTop :=
    (tendsto_rpow_atTop hν'p).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, Q ≤ n ∧ 1 ≤ n ∧ C ≤ (n : ℝ) ^ (p - ν') :=
    (eventually_ge_atTop Q).and ((eventually_ge_atTop 1).and
      (hpow.eventually (eventually_ge_atTop C)))
  obtain ⟨n, ⟨m, -, hlt⟩, hQn, hn1, hCn⟩ := (hC.and_eventually hev).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlow := hQ m n hQn
  have hrpow : (n : ℝ) ^ (-ν') = (n : ℝ) ^ (p - ν') / (n : ℝ) ^ p := by
    rw [← Real.rpow_sub hnpos]; congr 1; ring
  have hlt' : (n : ℝ) ^ (p - ν') / (n : ℝ) ^ p < C / (n : ℝ) ^ p := by
    rw [← hrpow]; exact lt_of_le_of_lt hlow hlt
  have hnp : (0 : ℝ) < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos p
  have := (div_lt_div_iff_of_pos_right hnp).mp hlt'
  linarith

theorem log_not_liouvilleWith_of_globalInterpolation (α : ℚ) (hα : 0 < α) (hα1 : α ≠ 1)
    (hgeometry : DeterminantContradiction.GlobalInterpolationStatement α)
    {p : ℝ} (hp : 2 < p) : ¬ LiouvilleWith p (Real.log α) :=
  not_liouvilleWith_of_eventualLowerBound
    (logEventualLowerBound_of_globalInterpolation α hα hα1 hgeometry) hp

end LogExponent

end OAI
