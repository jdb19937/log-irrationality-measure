import Mathlib
import OAI.NumberTheory.LogExponent.Approximation.AdmissibleParameters
import OAI.NumberTheory.LogExponent.Approximation.Comparison
import OAI.NumberTheory.LogExponent.Approximation.MatrixArithmetic
import OAI.NumberTheory.LogExponent.Approximation.MatrixCounting
import OAI.NumberTheory.LogExponent.Statement

namespace OAI

open Filter
open scoped Topology

namespace LogExponent.DeterminantContradiction

noncomputable def collisionConstant : ℝ := Real.log 2 / 4

theorem collisionConstant_pos : 0 < collisionConstant := by
  unfold collisionConstant
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev FixedData (α : ℚ) (nu : ℝ) := AdmissibleParameters α nu Arithmetic.lcmConstant collisionConstant

noncomputable def finiteNumerators {α : ℚ} {nu : ℝ} (d : FixedData α nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {α : ℚ} {nu : ℝ} (d : FixedData α nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

theorem finiteDenominators_two_le {α : ℚ} {nu : ℝ} (d : FixedData α nu) (i : Fin d.m) :
    2 ≤ finiteDenominators d i := (d.approximations i.val).1

theorem logWeights_eq {α : ℚ} {nu : ℝ} (d : FixedData α nu) (i : Fin d.m) :
    MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) :=
  (d.x_log i.val).symm

abbrev Row {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  InterpolationMatrix.truncatedLogMatrix (α : ℂ) d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  MatrixArithmetic.selectedMinor α d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {α : ℚ} {nu : ℝ} (d : FixedData α nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

theorem actual_minor_arithmetic_lower_bound {α : ℚ} {nu : ℝ} (d : FixedData α nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hh := MatrixArithmetic.selectedMinor_arithmetic_lower_bound α
    (finiteNumerators d) (finiteDenominators d) (finiteDenominators_two_le d)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [logWeights_eq]; exact d.wstar_lower i) selection hdet
  simpa only [actualMinor, actualMean, actualRowCount,
    AdmissibleParameters.arithmeticError, logWeights_eq] using hh

theorem actualMean_bounds {α : ℚ} {nu : ℝ} (d : FixedData α nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : ℝ) := by
  exact ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta (finiteDenominators d)
      (finiteDenominators_two_le d) (Nat.zero_lt_of_lt d.K_pos)
      d.v0_pos d.base.theta_pos hH⟩

/-- The interpolation hypothesis (Theorem 2.1′ of the paper, in the matrix form (3.3′)):
for the centres `(α^j, j p_i / q_i)` and jets along `Y = α^j (1 + t)`, the evaluation
matrix has full row rank for arbitrarily large `H`. -/
def GlobalInterpolationStatement (α : ℚ) : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData α nu,
    ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin

def AnalyticAggregateStatement (α : ℚ) : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData α nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          d.analyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

theorem tendsto_collisionRate {α : ℚ} {nu : ℝ} (d : FixedData α nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hA : 0 < d.base.A := by exact_mod_cast d.base.A_pos
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.base.theta d.base.A
    (finiteDenominators d) hv ht hA (finiteDenominators_two_le d)
    collisionConstant d.base.eta
  have he : collisionConstant * d.base.eta ^ 2 * (d.K : ℝ) *
      (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m) =
        collisionLimit d := by
    unfold collisionLimit
    ring
  rw [he] at hh
  exact hh

theorem no_fixed_data_of_interpolation_and_analytic_aggregate {α : ℚ}
    (hgeometry : GlobalInterpolationStatement α) (hanalytic : AnalyticAggregateStatement α)
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData α nu) : False := by
  classical
  obtain ⟨error, herror, hupper⟩ := hanalytic nu hnu d
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ =>
      collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit d - (1 + d.arithmeticError + d.analyticError + 0))) :=
    (tendsto_collisionRate d).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change 1 + d.arithmeticError + d.analyticError < collisionLimit d at hh
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, hupper,
      eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hupper hH
    intro hsurj
    obtain ⟨selection, _hselection, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix d H) hsurj
    have hdet' : (actualMinor d H selection).det ≠ 0 := hdet
    have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'
    have hb := actualMean_bounds d H hH
    exact determinant_bounds_inconsistent nu d.base.theta
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean d H)
      d.arithmeticError d.analyticError (error H) (collisionRate d H)
      (Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H))
      (by linarith) hb.1 hb.2 hsmall (by linarith) hlower (hupper selection hdet')
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := hgeometry nu hnu d L
  exact hL H hLH hsurj

theorem logEventualLowerBound_of_interpolation_and_analytic_aggregate (α : ℚ)
    (hα : Real.log α ≠ 0)
    (hgeometry : GlobalInterpolationStatement α) (hanalytic : AnalyticAggregateStatement α) :
    LogEventualLowerBound α := by
  intro nu hnu
  by_contra h
  push Not at h
  have hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.log α - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, herr⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, (le_max_left _ _).trans hq, herr.le⟩
  obtain ⟨d⟩ := exists_admissible_parameters α nu Arithmetic.lcmConstant collisionConstant
    hnu Arithmetic.lcmConstant_pos collisionConstant_pos hα hbad
  exact no_fixed_data_of_interpolation_and_analytic_aggregate hgeometry hanalytic nu hnu d

end LogExponent.DeterminantContradiction

end OAI
