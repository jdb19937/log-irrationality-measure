import LogIrrationalityMeasure.Ampleness.AdmissibleBlowupGeometry
import LogIrrationalityMeasure.Approximation.DeterminantContradiction
import LogIrrationalityMeasure.Approximation.FormalMatrixSurjectivity
import LogIrrationalityMeasure.Approximation.WeightedSliceDegree

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.AdmissibleMatrixInterpolation
open Filter
open DeterminantContradiction AdmissibleBlowupGeometry
variable {α : ℚ} {ν : ℝ} (d : FixedData α ν)

theorem degreeWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveDegreeWeights i : ℝ) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveDegreeWeights_succ,
      d.cast_rationalWeight, InterpolationMatrix.columnWeights, Fin.cases_succ,
      logWeights_eq]

theorem jetWeights_eq_matrix (i : Fin (d.m+1)) :
    (d.curveJetWeights i : ℝ) =
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, InterpolationMatrix.rowWeights, Fin.cases_succ,
      logWeights_eq]

theorem actual_truncation_weight_bound (i : Fin d.m) :
    d.curveJetWeights i.succ ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) *
        d.curveJetWeights 0 := by
  have hw : 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    rw [logWeights_eq]
    exact zero_lt_one.trans_le (d.x_one_le _)
  have hF : 1 / (d.base.theta : ℝ) < d.F0 :=
    (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) d.base.theta_pos).trans d.F0_large
  have hceil := Nat.le_ceil
    (d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i / (d.v0 : ℝ))
  have hbound : MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.v0 : ℝ) := by
    calc
      _ = (1 / (d.base.theta : ℝ)) *
          MatrixArithmetic.logWeights (finiteDenominators d) i := by ring
      _ ≤ d.F0 * MatrixArithmetic.logWeights (finiteDenominators d) i :=
        mul_le_mul_of_nonneg_right hF.le hw.le
      _ ≤ _ := (div_le_iff₀ d.v0_pos).mp hceil
  have hcast : (d.curveJetWeights i.succ : ℝ) ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
        (d.curveJetWeights 0 : ℝ) := by
    simpa only [AdmissibleParameters.curveJetWeights_zero,
      AdmissibleParameters.curveJetWeights_succ, Rat.cast_div,
      d.cast_rationalWeight, logWeights_eq] using hbound
  exact_mod_cast hcast

theorem matrix_degree_of_supportBound (H : ℝ) (P : LogExponentApprox.FramePolynomial d.m)
    (hP : WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ)) H P) :
    LogExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d))) H P := by
  intro a ha
  have h := hP a ha
  have hw : (fun i => (d.curveDegreeWeights i : ℝ)) =
      InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) :=
    funext (degreeWeights_eq_matrix d)
  rw [hw] at h
  simpa only [LogExponentApprox.monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul] using h

theorem curveCenters_eq_rowCenter (j : Fin d.K) :
    d.curveCenters j = FormalMatrixBridge.rowCenter (α : ℂ)
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) j.val := rfl

theorem actualMatrix_surjective_of_formalPackets {β : Type*} (H : ℚ)
    (P : β → LogExponentApprox.FramePolynomial d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights H
        (FormalLogJet.formalJet (d.curveCenters j) (P a)))) :
    Function.Surjective (actualMatrix d (H : ℝ)).mulVecLin := by
  apply FormalMatrixBridge.truncatedLogMatrix_surjective_of_formalLog_packets
    (α : ℂ) d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    d.w0_pos (fun i => ?_) d.curveJetWeights d.curveJetWeights_pos
    (jetWeights_eq_matrix d)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (actual_truncation_weight_bound d) P
    (fun a => matrix_degree_of_supportBound d _ _ (hdegree a))
    (by simpa only [curveCenters_eq_rowCenter] using hpacket)
  rw [logWeights_eq]
  exact zero_lt_one.trans_le (d.x_one_le _)

def WeightedPolynomials (n : ℕ) :=
  {P : LogExponentApprox.FramePolynomial d.m //
    WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) :=
  fun j : Fin d.K => JetGeometry.rationalCoefficientPacket d.curveJetWeights
    ((n : ℚ) * (scale d).radius) (FormalLogJet.formalJet (d.curveCenters j) P.val)

theorem packetMap_surjective_of_family {β : Type*} (n : ℕ)
    (P : β → LogExponentApprox.FramePolynomial d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ) * (scale d).radius) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights
        ((n : ℚ) * (scale d).radius) (FormalLogJet.formalJet (d.curveCenters j) (P a)))) :
    Function.Surjective (packetMap d n) := by
  intro y
  obtain ⟨a,ha⟩ := hpacket y
  exact ⟨⟨P a,hdegree a⟩,ha⟩

theorem actualMatrix_surjective_of_packetMap (n : ℕ)
    (hpacket : Function.Surjective (packetMap d n)) :
    Function.Surjective (actualMatrix d ((n : ℝ) * (scale d).radius)).mulVecLin := by
  have h := actualMatrix_surjective_of_formalPackets d
    ((n : ℚ) * (scale d).radius) (fun P : WeightedPolynomials d n => P.val)
    (fun P => by simpa only [Rat.cast_mul, Rat.cast_natCast] using P.property) hpacket
  have hc : (((n : ℚ) * (scale d).radius : ℚ) : ℝ) =
      (n : ℝ) * (scale d).radius := by push_cast; rfl
  exact hc ▸ h

theorem cofinal_actualMatrix_of_eventual_packets
    (hpacket : ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n))
    (L : ℝ) : ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hpacket
  let n := max N (Nat.ceil (L / ((scale d).radius : ℝ)))
  have hR : (0 : ℝ) < (scale d).radius := by exact_mod_cast (scale d).radius_pos
  have hL : L ≤ (n : ℝ) * (scale d).radius := by
    apply (div_le_iff₀ hR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right N
      (Nat.ceil (L / ((scale d).radius : ℝ)))))
  exact ⟨(n : ℝ) * (scale d).radius, hL,
    actualMatrix_surjective_of_packetMap d n (hN n (le_max_left _ _))⟩

theorem globalInterpolation_of_eventual_packets
    (hpacket : ∀ ν : ℝ, 2 < ν → ∀ d : FixedData α ν,
      ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n)) :
    GlobalInterpolationStatement α := by
  intro ν hν d L
  exact cofinal_actualMatrix_of_eventual_packets d (hpacket ν hν d) L

end LogExponent.AdmissibleMatrixInterpolation

end

end LogIrrationalityMeasure
