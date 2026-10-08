import OAI.NumberTheory.LogExponent.Geometry.AdmissibleCurveWeights
import OAI.NumberTheory.LogExponent.Geometry.CurveInequality
import OAI.NumberTheory.LogExponent.Geometry.CurvePrimeHeight
import OAI.NumberTheory.LogExponent.Geometry.PlaceLocalRing

namespace OAI

noncomputable section
open scoped BigOperators
namespace LogExponent.CurveInequality

open CurveValuationCenter PlaceValuationRing CurveContactFamily PersistentWeightComparison


variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

variable [Algebra.EssFiniteType ℂ E]

theorem weighted_curve_inequality {m K : ℕ}
    (y : E) (x : Fin m → E) (c : Fin K → Fin (m+1) → ℂ)
    (hc : Function.Injective (fun j => c j 0)) (hc0 : ∀ j, c j 0 ≠ 0)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  dsimp only
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (m+1) → E := Fin.cases y x
  have hz := nonconstant_coordinates z hgen htrdeg
  change (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
    (contact hres hfinite z c hz v p : ℝ) ≤ CurveContactSum.weightedDegree hfinite z w
  by_contra h
  have hexcess := lt_of_not_ge h
  obtain ⟨p0, hp0⟩ := places_nonempty_of_excess hres hfinite z c hz w v sigma hexcess
  have hy := excess_implies_zeroth_constant hres hfinite z c hc0 hz
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv sigma hsigma hvol hseparated hexcess p0 hp0
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin K, y = algebraMap ℂ E (c j0 0) := ⟨_, hy⟩
  subst hj0
  exact no_fibre_excess_of_zeroth_constant hres hfinite (c j0 0) x c hc hc0 hz
    w v hw hv sigma hsigma hratio j0 rfl hexcess

theorem admissible_weighted_curve_inequality {α : ℚ} {nu Lambda C : ℝ}
    (d : AdmissibleParameters α nu Lambda C)
    (y : E) (x : Fin d.m → E) (c : Fin d.K → Fin (d.m+1) → ℂ)
    (hc : Function.Injective (fun j => c j 0)) (hc0 : ∀ j, c j 0 ≠ 0)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
      (contact hres hfinite z c hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  weighted_curve_inequality y x c hc hc0 hgen htrdeg
    d.curveDegreeWeights d.curveJetWeights d.curveDegreeWeights_pos d.curveJetWeights_pos
    d.sigma (by exact_mod_cast d.sigma_pos) d.curve_volume
    d.curve_separated_weight_products d.curve_coordinate_ratio

end LogExponent.CurveInequality
end

end OAI
