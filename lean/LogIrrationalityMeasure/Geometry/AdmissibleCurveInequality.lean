import LogIrrationalityMeasure.Approximation.MatrixArithmetic
import LogIrrationalityMeasure.Geometry.CurveInequalityIntrinsic

namespace LogIrrationalityMeasure

noncomputable section
open scoped BigOperators
namespace LogExponent.AdmissibleParameters

variable {α : ℚ} {nu Lambda C : ℝ} (d : AdmissibleParameters α nu Lambda C)
include d

theorem nu_gt_one : 1 < nu := by
  have h1 := d.base.theta_lt_A
  have h2 := d.base.A_lt_B
  have h3 := d.base.B_lt_one
  have h4 := d.base.approximation_gap
  by_contra h
  push_neg at h
  have hpos : (0 : ℝ) < (d.base.A : ℝ) - d.base.theta := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h hpos.le]

theorem log_ne_zero : Real.log α ≠ 0 := by
  intro h0
  obtain ⟨hq, hp, happ⟩ := d.approximations 0
  have hq0 : (0 : ℝ) < d.q 0 := by exact_mod_cast (show 0 < d.q 0 by omega)
  have hq1 : (1 : ℝ) < d.q 0 := by exact_mod_cast (show 1 < d.q 0 by omega)
  rw [h0, zero_sub, abs_neg, abs_div, Nat.abs_cast] at happ
  have hp1 : (1 : ℝ) ≤ |(d.p 0 : ℝ)| := by
    have := Int.one_le_abs hp
    exact_mod_cast this
  have hlow : (d.q 0 : ℝ) ^ (-(1 : ℝ)) ≤ |(d.p 0 : ℝ)| / d.q 0 := by
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact div_le_div_of_nonneg_right hp1 hq0.le
  have hstrict : (d.q 0 : ℝ) ^ (-nu) < (d.q 0 : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith [d.nu_gt_one])
  linarith

theorem cast_ne_zero : (α : ℂ) ≠ 0 := by
  intro h
  apply d.log_ne_zero
  have : α = 0 := by exact_mod_cast h
  simp [this]

theorem abs_ne_one : |(α : ℝ)| ≠ 1 := by
  intro h
  apply d.log_ne_zero
  rw [← Real.log_abs, h, Real.log_one]

/-- The centres `(α^j, j p_i / q_i)`. -/
def curveCenters : Fin d.K → Fin (d.m+1) → ℂ :=
  fun j => Fin.cases ((α : ℂ) ^ j.val) (fun i => (j.val : ℂ) *
    MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i)

@[simp] theorem curveCenters_zero (j : Fin d.K) : d.curveCenters j 0 = (α : ℂ) ^ j.val := rfl

@[simp] theorem curveCenters_succ (j : Fin d.K) (i : Fin d.m) :
    d.curveCenters j i.succ = (j.val : ℂ) *
      MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
        (fun i : Fin d.m => d.q i.val) i := rfl

theorem curveCenters_zero_ne_zero (j : Fin d.K) : d.curveCenters j 0 ≠ 0 :=
  pow_ne_zero _ d.cast_ne_zero

theorem curveCenters_zero_injective : Function.Injective (fun j => d.curveCenters j 0) := by
  intro j l h
  simp only [curveCenters_zero] at h
  have hR : ((α : ℝ) ^ j.val : ℝ) = (α : ℝ) ^ l.val := by
    have h' : (((α : ℝ) ^ j.val : ℝ) : ℂ) = (((α : ℝ) ^ l.val : ℝ) : ℂ) := by
      push_cast
      exact h
    exact_mod_cast h'
  have habs : |(α : ℝ)| ^ j.val = |(α : ℝ)| ^ l.val := by
    rw [← abs_pow, ← abs_pow, hR]
  have hpos : 0 < |(α : ℝ)| := by
    apply abs_pos.mpr
    intro h0
    apply d.log_ne_zero
    simp [h0]
  exact Fin.ext (pow_right_injective₀ hpos d.abs_ne_one habs)

theorem curveCenters_succ_injective (i : Fin d.m) :
    Function.Injective (fun j => d.curveCenters j i.succ) := by
  have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    exact_mod_cast (show d.q i.val ≠ 0 by have := (d.approximations i.val).1; omega)
  have hr : MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i ≠ 0 := by
    unfold MatrixArithmetic.rationalCenters
    exact div_ne_zero hp hq
  intro j l h
  simp only [curveCenters_succ] at h
  have he := (mul_right_cancel₀ hr h : (j.val : ℂ) = (l.val : ℂ))
  apply Fin.ext
  exact_mod_cast he

theorem curveCenters_injective : Function.Injective d.curveCenters := by
  intro j l h
  exact d.curveCenters_zero_injective (congrFun h 0)

theorem exact_weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  CurveInequality.admissible_weighted_curve_inequality d y x d.curveCenters
    d.curveCenters_zero_injective d.curveCenters_zero_ne_zero hgen htrdeg

end LogExponent.AdmissibleParameters
end

end LogIrrationalityMeasure
