import Mathlib
import LogIrrationalityMeasure.Approximation.Parameters
import LogIrrationalityMeasure.Approximation.Sigma
import LogIrrationalityMeasure.Approximation.SuccessiveApproximations
import LogIrrationalityMeasure.Approximation.WeightErrorMargin
import LogIrrationalityMeasure.Approximation.WeightSeparation
import LogIrrationalityMeasure.Approximation.WeightSeparationConstant
import LogIrrationalityMeasure.LocalAlgebra.Dimension

namespace LogIrrationalityMeasure

namespace LogExponent

noncomputable def interpolationSeparationConstant (m : ℕ) (sigma : ℚ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) *
    (1 + ((m : ℝ) + 2) / (sigma : ℝ)) ^ (m + 2)

theorem interpolationSeparationConstant_pos (m : ℕ) (sigma : ℚ)
    (hsigma : 0 < (sigma : ℝ)) : 0 < interpolationSeparationConstant m sigma := by
  unfold interpolationSeparationConstant
  positivity

/-- The collision radius `R_α = 100 K (1 + |log α|)` of Lemma 3.3′. -/
noncomputable def centerRadius (α : ℚ) (K : ℕ) : ℝ := 100 * K * (1 + |Real.log α|)

theorem one_le_centerRadius (α : ℚ) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ centerRadius α K := by
  unfold centerRadius
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [abs_nonneg (Real.log α)]

/-- The constant `100 (1 + |log α|) + log b` (with `α = a / b`) multiplying `K / w₀`
in the dimension margin: it dominates both `R_α / w₀` and `(K − 1) log b / w₀`. -/
noncomputable def centerErrorConstant (α : ℚ) : ℝ :=
  100 * (1 + |Real.log α|) + Real.log α.den

theorem centerErrorConstant_nonneg (α : ℚ) : 0 ≤ centerErrorConstant α := by
  unfold centerErrorConstant
  have := Real.log_natCast_nonneg α.den
  nlinarith [abs_nonneg (Real.log α)]

noncomputable def weightErrorCoefficient (nu theta : ℝ) (K : ℕ) (α : ℚ) : ℝ :=
  theta + Real.log 4 + Real.log (2 * (K : ℝ)) + nu + Real.log (2 * centerRadius α K)

theorem weightErrorCoefficient_nonneg (nu theta : ℝ) (K : ℕ) (α : ℚ)
    (hnu : 0 < nu) (htheta : 0 < theta) (hK : 1 ≤ K) :
    0 ≤ weightErrorCoefficient nu theta K α := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2K : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
  have hR := one_le_centerRadius α hK
  have h2R : 0 ≤ Real.log (2 * centerRadius α K) := Real.log_nonneg (by linarith)
  unfold weightErrorCoefficient
  linarith

theorem exists_initial_scale (nu theta epsilon : ℝ) (_htheta : 0 < theta)
    (hepsilon : 0 < epsilon) :
    ∃ F0 : ℝ, 0 < F0 ∧ 2 / theta < F0 ∧ nu / F0 < epsilon / 3 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (2 / theta) (3 * nu / epsilon)))
  have hF : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hthetaF : 2 / theta < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have hnuF : 3 * nu / epsilon < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  refine ⟨N, by linarith, hthetaF, ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < N by linarith)).2
  have := (div_lt_iff₀ hepsilon).mp hnuF
  nlinarith

structure AdmissibleParameters (α : ℚ) (nu Lambda c : ℝ) where
  base : Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      centerErrorConstant α * (K : ℝ) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1
  x_zero : x 0 = 1
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |Real.log α - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  weight_growth : LogExponentApprox.SeparatedWeightGrowth m
    (LogExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) x
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = x (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
    weightErrorCoefficient nu base.theta K α / wstar < epsilon / 3

theorem exists_admissible_parameters (α : ℚ)
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hα : Real.log α ≠ 0)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.log α - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters α nu Lambda c) := by
  classical
  obtain ⟨P⟩ := exists_parameters nu hnu
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hdim, hcollision⟩ := exists_dimension_margin
    P.theta P.A P.B P.C P.eta (Lambda * F0) (2 * Real.log 2) (centerErrorConstant α)
    (epsilon / 3) (2 / c) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos hLambda hF0).le (by positivity) (centerErrorConstant_nonneg α) heps3
  let K : ℕ := dimensionK P.C m
  let w0 : ℚ := (P.B ^ m)⁻¹
  let v0 : ℚ := 2 * (K : ℚ) * P.theta ^ m * w0
  have hK : 1 ≤ K := dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = dimensionW P.B m := by simp [w0, dimensionW]
  have hv0eq : (v0 : ℝ) = dimensionV P.theta P.B P.C m := by
    simp [v0, dimensionV, K, hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by
    rw [hw0eq]
    exact dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ) * ((w0 : ℝ) / v0) * (P.theta : ℝ) ^ m = 1 / 2 := by
    rw [hw0eq, hv0eq]
    exact dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 2 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 2 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  have hnupos : 0 < nu := by linarith
  have hS : 0 ≤ weightErrorCoefficient nu P.theta K α :=
    weightErrorCoefficient_nonneg nu P.theta K α hnupos P.theta_pos hK
  obtain ⟨X, hX, hXmargin⟩ := exists_uniform_weight_error_margin m Lambda
    (weightErrorCoefficient nu P.theta K α) (epsilon / 3) hLambda hS heps3
  obtain ⟨p, q, x, hx0, hxlog, happ, hx1, hgrowth⟩ :=
    exists_normalized_successive_approximations (Real.log α) hα nu X
      (LogExponentApprox.weightSeparationFactor m
        (interpolationSeparationConstant m sigma) w0 v0 P.theta) hnupos hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    exists_minimum_weight m hm (fun i : Fin m => x (i.val + 1)) X
      (fun i => (happ i.val).2.2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  refine ⟨{
    base := P
    epsilon := epsilon
    F0 := F0
    m := m
    K := K
    w0 := w0
    v0 := v0
    sigma := sigma
    p := p
    q := q
    x := x
    wstar := wstar
    epsilon_pos := hepsilon
    epsilon_lt_gap := hepsg
    epsilon_le_half := hepshalf
    F0_pos := hF0
    F0_large := hFtheta
    initial_margin := hFmargin
    m_pos := hm
    K_eq := rfl
    K_pos := hK
    w0_eq := hw0eq
    v0_eq := hv0eq
    w0_pos := hw0
    v0_pos := hv0
    volume_eq := hvolume
    volume_lt_one := hvolume1
    dimension_margin := ?_
    collision_margin := hcollision'
    sigma_pos := hsigma
    sigma_volume := ?_
    sigma_centers := hsigmaK
    sigma_theta := hsigmaTheta
    x_zero := hx0
    x_log := hxlog
    approximations := fun n => ⟨(happ n).1, (happ n).2.1, (happ n).2.2.1⟩
    x_one_le := hx1
    weight_growth := fun i hi _ => hgrowth i hi
    wstar_pos := hwstar
    wstar_lower := hwstarLower
    wstar_attained := hwstarAttained
    weight_margin := hXmargin wstar (fun i : Fin m => x (i.val + 1))
      hwstarX hwstarLower
  }⟩
  · rw [hv0eq, hw0eq]
    exact hdim
  · rw [hvolume]
    exact hsigmaVol

namespace AdmissibleParameters

variable {α : ℚ} {nu Lambda c : ℝ} (d : AdmissibleParameters α nu Lambda c)

noncomputable def rationalWeight : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (d.q n)) : ℚ)

theorem cast_rationalWeight (i : ℕ) : (d.rationalWeight i : ℝ) = d.x i := by
  cases i with
  | zero => simpa [rationalWeight] using d.x_zero.symm
  | succ n => simpa [rationalWeight] using (d.x_log n).symm

theorem rationalWeight_pos (i : ℕ) : 0 < d.rationalWeight i := by
  have h : (0 : ℝ) < (d.rationalWeight i : ℝ) := by
    rw [d.cast_rationalWeight]
    exact zero_lt_one.trans_le (d.x_one_le i)
  exact_mod_cast h

theorem multiplicity_constant_bound (k : ℕ) (hk : k ≤ d.m) :
    2 * (k.factorial : ℝ) * (((d.m : ℝ) + 2) / (d.sigma : ℝ)) ^ k ≤
      interpolationSeparationConstant d.m d.sigma := by
  exact LogExponentApprox.multiplicity_constant_le_enlarged d.m k d.sigma d.sigma_pos hk

theorem rectangular_multiplicity_constant_bound (k : ℕ) (hk : k ≤ d.m) :
    (k : ℝ) ^ k * (((d.m : ℝ) + 2) / (d.sigma : ℝ)) ^ k ≤
      interpolationSeparationConstant d.m d.sigma := by
  exact LogExponentApprox.rectangular_multiplicity_constant_le_enlarged
    d.m k d.sigma d.sigma_pos hk

theorem separated_weight_products
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (d.m + 1)) (hB : B ⊆ Finset.range (d.m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    interpolationSeparationConstant d.m d.sigma *
      (∏ j ∈ B, LogExponentApprox.geometricJetWeight d.v0 d.base.theta d.x j) <
      ∏ j ∈ A, LogExponentApprox.geometricDegreeWeight d.w0 d.x j := by
  exact LogExponentApprox.geometric_weight_products_separated d.m
    (interpolationSeparationConstant d.m d.sigma) d.w0 d.v0 d.base.theta d.x
    (interpolationSeparationConstant_pos d.m d.sigma d.sigma_pos)
    d.w0_pos d.v0_pos d.base.theta_pos d.x_zero d.x_one_le d.weight_growth
    A B hcard hA hB i hi hiA hiB hbelow

theorem total_error_lt_gap :
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K α / d.wstar) <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
        (1 - d.base.theta) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_lt_gap
  linarith

theorem collision_exceeds_one_add_error :
    1 + (nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K α / d.wstar)) <
      c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
        (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_le_half
  have h5 := d.collision_margin
  linarith

/-- The arithmetic error `E'_ar` of Lemma 3.1′, including `(K − 1) log b / w₀`. -/
noncomputable def arithmeticError : ℝ :=
  Lambda * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) +
    Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) + (d.base.theta : ℝ) / d.wstar +
    ((d.K : ℝ) - 1) * Real.log α.den / (d.w0 : ℝ)

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

/-- The holomorphic error `E'_hol` of Lemma 3.3′, with radius `R_α`. -/
noncomputable def holomorphicError : ℝ :=
  centerRadius α d.K / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    Real.log (2 * centerRadius α d.K) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError

theorem center_errors_le :
    ((d.K : ℝ) - 1) * Real.log α.den / (d.w0 : ℝ) + centerRadius α d.K / (d.w0 : ℝ) ≤
      centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ) := by
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ d.w0_pos.le
  have hlog : 0 ≤ Real.log α.den := Real.log_natCast_nonneg α.den
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  unfold centerRadius centerErrorConstant
  nlinarith [abs_nonneg (Real.log α)]

theorem error_sum_le : d.arithmeticError + d.analyticError ≤
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K α / d.wstar) := by
  have hdiff : (nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta d.K α / d.wstar)) -
      (d.arithmeticError + d.analyticError) =
      centerErrorConstant α * (d.K : ℝ) / (d.w0 : ℝ) -
        (((d.K : ℝ) - 1) * Real.log α.den / (d.w0 : ℝ) +
          centerRadius α d.K / (d.w0 : ℝ)) := by
    unfold arithmeticError analyticError translationError holomorphicError
      weightErrorCoefficient
    ring
  have h := d.center_errors_le
  linarith

theorem error_sum_lt_gap : d.arithmeticError + d.analyticError <
    nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
      (1 - d.base.theta) :=
  lt_of_le_of_lt d.error_sum_le d.total_error_lt_gap

theorem collision_exceeds_error_sum : 1 + d.arithmeticError + d.analyticError <
    c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  have h1 := d.error_sum_le
  have h2 := d.collision_exceeds_one_add_error
  linarith

end AdmissibleParameters

end LogExponent

end LogIrrationalityMeasure
