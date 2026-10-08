import OAI.NumberTheory.LogExponent.Approximation.FibreWeightSeparation
import OAI.NumberTheory.LogExponent.Cohomology.CurveDerivativeVanishing
import OAI.NumberTheory.LogExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.LogExponent.Jets.FormalAuxiliaryJet
import OAI.NumberTheory.LogExponent.Jets.OrdinaryAuxiliaryJet
import OAI.NumberTheory.LogExponent.LocalAlgebra.CoordinateContactBound

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace LogExponent.CurveInequality

open LogExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison


theorem places_nonempty_of_excess
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (sigma : ℚ)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    (places hfinite z c hz).Nonempty := by
  by_contra h
  have he : places hfinite z c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  rw [he, Finset.sum_empty, mul_zero] at hexcess
  exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess

/-- Excess contact forces the `Y`-coordinate of the curve to be the `Y`-coordinate of the
centre of any of its contact places. -/
theorem excess_implies_zeroth_constant
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    z 0 = algebraMap ℂ E (c (center hfinite z c hz p hp) 0) := by
  have hvR (i : Fin (m+1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := eventually_exists_formalJet_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles (m+1) (fun i => (v i : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := CurveDerivativeVanishing.logarithmic_words_vanish hres hfinite z c hc0 hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  exact CurveFieldRigidity.logarithmic_coordinate_constant z
    (c (center hfinite z c hz p hp)) (hc0 _) p
    (centered hfinite z c hz p hp) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated

/-- A curve in the fibre `Y = c j0 0` has no excess contact: all its contact places are
centred at `j0`, and the coordinate-power bound closes. -/
theorem no_fibre_excess_of_zeroth_constant
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (x : Fin m → E) (c : Fin K → Fin (m+1) → ℂ)
    (hc : Function.Injective (fun j => c j 0)) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (j0 : Fin K) (ha : a = c j0 0) :
    ¬ CurveContactSum.weightedDegree hfinite (fibre a x) w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre a x) c hz,
        (contact hres hfinite (fibre a x) c hz v p : ℝ) := by
  subst ha
  intro hexcess
  let z : Fin (m+1) → E := fibre (c j0 0) x
  let S := places hfinite z c hz
  let μ := fun p => (contact hres hfinite z c hz v p : ℝ)
  have hdeg : CurveContactSum.weightedDegree hfinite (fibre (c j0 0) x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) :=
    FibreContact.weightedDegree_const hfinite (c j0 0) w x
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p := by
    rw [hdeg] at hexcess
    exact hexcess
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1+sigma := by exact_mod_cast (by linarith : (0 : ℚ)<1+sigma)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hcenters : ∀ p (hp : p ∈ S), center hfinite z c hz p hp = j0 := by
    intro p hp
    apply hc
    exact ((centered hfinite z c hz p hp).constant_coordinate 0 (c j0 0) rfl).symm
  have hcenter : ∀ p ∈ S, CurveCenters.Centered x (fun i => c j0 i.succ) p := by
    intro p hp i
    simpa only [hcenters p hp, z, fibre_succ] using
      centered hfinite z c hz p hp i.succ
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i.succ) :=
    PlaceCenteredBranch.fibre_nonconstant x (c j0) (nonconstant z (c j0) hz)
  obtain ⟨i,hi⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x (fun i => c j0 i.succ)
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ)
    i (sub_ne_zero.mpr hi) S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have heq := contact_fibre hres hfinite (c j0 0) (hc0 j0) x c hz v p hp
      have hcongr {a b : Fin m → ℂ} (hab : a = b)
          (ha : CurveCenters.Centered x a p) (hna : ∃ i, x i ≠ algebraMap ℂ E (a i))
          (hb : CurveCenters.Centered x b p) (hnb : ∃ i, x i ≠ algebraMap ℂ E (b i)) :
          PlaceCenteredBranch.ordinaryContact p x a ha hna (fun i => v i.succ) =
            PlaceCenteredBranch.ordinaryContact p x b hb hnb (fun i => v i.succ) := by
        subst b
        rfl
      have hcontact := heq.trans (hcongr
        (funext (fun i => congrArg (fun j => c j i.succ) (hcenters p hp))) _ _
        (hcenter p hp) ⟨i, hi⟩)
      exact congrArg (fun q : ℚ => (q : ℝ)) hcontact)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hex hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

end LogExponent.CurveInequality
end

end OAI
