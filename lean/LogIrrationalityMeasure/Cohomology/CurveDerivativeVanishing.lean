import LogIrrationalityMeasure.Geometry.CurveContactFamily
import LogIrrationalityMeasure.Geometry.CurveFieldRigidity

namespace LogIrrationalityMeasure

noncomputable section
open scoped BigOperators
namespace LogExponent.CurveDerivativeVanishing

open LogExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = (word.map (fun i => (v i : ℝ))).sum := by
  induction word with
  | nil => simp
  | cons i word ih => simp [ih]

theorem logarithmic_words_vanish
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    ∀ word : List (Fin (m+1)),
      frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (word.map v).sum ≤ sigma*N := by
    change (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N at hword
    rw [← cast_word_cost v word] at hword
    exact_mod_cast hword
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mp
    exact hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
  have hsum : 0 ≤ ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact_mod_cast contact_nonneg hres hfinite z c hc0 hz v hv p
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree
    (places hfinite z c hz) (fun p => (contact hres hfinite z c hz v p : ℝ))
  · intro hne p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by
      nlinarith
    have hlocal := logWord_order_lower hres hfinite z c hc0 hz v hv ((1+3*sigma)*N)
      F hjet word hne p hp
    have hq := (mul_le_mul_of_nonneg_left hret
      (contact_nonneg hres hfinite z c hc0 hz v hv p)).trans hlocal
    have hr : (contact hres hfinite z c hz v p : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
            (contact hres hfinite z c hz v p : ℝ)) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

end LogExponent.CurveDerivativeVanishing
end

end LogIrrationalityMeasure
