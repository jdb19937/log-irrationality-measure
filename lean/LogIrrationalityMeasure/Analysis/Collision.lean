import LogIrrationalityMeasure.Analysis.AnalyticDeterminantCollision
import LogIrrationalityMeasure.Analysis.PeriodAnalytic
import LogIrrationalityMeasure.Polynomials.SimplexLog

namespace LogIrrationalityMeasure

open scoped BigOperators Topology
open Filter

namespace LogExponent

noncomputable def holomorphicError (K : ℕ) (w0 v0 wstar : ℝ) (ω : ℂ) : ℝ :=
  AnalyticCollision.collisionRadius K ω / w0 + Real.log 2 / v0 +
    Real.log (2 * AnalyticCollision.collisionRadius K ω) / wstar

theorem formal_period_collision_bound
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ω y : ℂ) (hy : Complex.exp ω = y)
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((MatrixTranslation.periodMonomial y (j r) ω
        (h c) (a c)).coeff (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (holomorphicError K w0 v0 wstar ω +
            Collision.collisionRemainder (Fintype.card ι) H)) := by
  let R : NNReal := ⟨AnalyticCollision.collisionRadius K ω,
    (AnalyticCollision.collisionRadius_pos hK ω).le⟩
  have hR : 0 < R := by
    change (0 : ℝ) < AnalyticCollision.collisionRadius K ω
    exact AnalyticCollision.collisionRadius_pos hK ω
  have hR1 : (1 : ℝ) ≤ R := AnalyticCollision.one_le_collisionRadius hK ω
  have hb := AnalyticCollision.translated_row_determinant_exp_bound
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ) * ω) ell R hR hH
    (fun A c => PeriodAnalytic.differentiable_columnFunction _ _ _)
    (A := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    (fun A c z hz => PeriodAnalytic.norm_columnFunction_le (h c) (a c) (transverse A) w
      hR1 hH.le hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => AnalyticCollision.period_center_radius_bound ω hK (hj r)) hell
  have hRv : (R : ℝ) = AnalyticCollision.collisionRadius K ω := rfl
  rw [hRv] at hb
  simp_rw [PeriodAnalytic.periodMonomial_coeff_eq_rowTest ω y hy]
  convert! hb using 1
  congr 1
  unfold holomorphicError
  ring

theorem tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring

end LogExponent

end LogIrrationalityMeasure
