import OAI.NumberTheory.LogExponent.Geometry.CurveContactSum
import OAI.NumberTheory.LogExponent.Jets.DVRBranchJet
import OAI.NumberTheory.LogExponent.Jets.OrdinaryDVRBranchJet
import OAI.NumberTheory.LogExponent.Polynomials.WeightedPolynomialPole

namespace OAI

noncomputable section
namespace LogExponent.FibreContact

theorem contact_zero_cons {m : ℕ} (v : Fin (m+1) → ℚ)
    (a : Fin m → PowerSeries ℂ) (ha : ∃ i, a i ≠ 0)
    (hfull : ∃ i, (Fin.cases 0 a : Fin (m+1) → PowerSeries ℂ) i ≠ 0) :
    BranchContact.contact v (Fin.cases 0 a) hfull =
      BranchContact.contact (fun i => v i.succ) a ha := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v i.succ) a ha
    have hh := BranchContact.contact_le v
      (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull i.succ
      (by simpa only [Fin.cases_succ] using hi)
    simp only [Fin.cases_succ] at hh
    exact hh.trans_eq he.symm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains v (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i =>
      have hh := BranchContact.contact_le (fun i => v i.succ) a ha i
        (by simpa only [Fin.cases_succ] using hi)
      simp only [Fin.cases_succ] at he
      exact hh.trans_eq he.symm

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem coordinates_fibre {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (x : Fin m → A) :
    DVRBranchJet.coordinates c (algebraMap ℂ A (c 0)) x =
      Fin.cases 0 (OrdinaryDVRBranchJet.coordinates (fun i => c i.succ) x) := by
  have h0 : FormalBranchEvaluation.centeredY c
      (DVRBranch.expansion ℂ A (algebraMap ℂ A (c 0))) = 0 := by
    rw [AlgHom.commutes]
    exact (FormalBranchEvaluation.centeredY_eq_zero_iff c hc _).mpr rfl
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates,
      Fin.cases_zero, h0]
  | succ i =>
    simp only [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates,
      Fin.cases_succ, h0,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero]
    rfl

theorem logarithmic_contact_eq_ordinary {m : ℕ} (v : Fin (m+1) → ℚ)
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (x : Fin m → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i.succ)) :
    DVRBranchJet.contact v c (algebraMap ℂ A (c 0)) x (Or.inr hnc) =
      OrdinaryDVRBranchJet.contact (fun i => v i.succ) (fun i => c i.succ) x hnc := by
  have ha := OrdinaryDVRBranchJet.coordinates_nonzero (fun i => c i.succ) x hnc
  have hb : ∃ i, (Fin.cases (0 : PowerSeries ℂ)
      (OrdinaryDVRBranchJet.coordinates (fun i => c i.succ) x) : Fin (m+1) → PowerSeries ℂ) i ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i.succ, by simpa only [Fin.cases_succ] using hi⟩
  have hcongr {b d : Fin (m+1) → PowerSeries ℂ} (he : b = d)
      (hb : ∃ i, b i ≠ 0) (hd : ∃ i, d i ≠ 0) :
      BranchContact.contact v b hb = BranchContact.contact v d hd := by subst d; rfl
  exact (hcongr (coordinates_fibre c hc x)
    (DVRBranchJet.coordinates_nonzero c _ x (Or.inr hnc)) hb).trans
      (contact_zero_cons v (OrdinaryDVRBranchJet.coordinates (fun i => c i.succ) x) ha hb)

theorem weightedPole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (t : ℚ) (ht : 0 ≤ t) (hcoord : ∀ i, -z i / w i ≤ t) :
    WeightedCurveDegree.weightedPole w z ≤ t := by
  apply Finset.sup'_le
  intro i hi
  cases i with
  | none => exact ht
  | some i => exact hcoord i

theorem weightedPole_zero_cons {m : ℕ} (w : Fin (m+1) → ℚ) (z : Fin m → ℚ) :
    WeightedCurveDegree.weightedPole w (Fin.cases 0 z) =
      WeightedCurveDegree.weightedPole (fun i => w i.succ) z := by
  let zz : Fin (m+1) → ℚ := Fin.cases 0 z
  let ww : Fin m → ℚ := fun i => w i.succ
  change WeightedCurveDegree.weightedPole w zz = WeightedCurveDegree.weightedPole ww z
  have hz0 : zz 0 = 0 := rfl
  have hzs (i : Fin m) : zz i.succ = z i := rfl
  have hws (i : Fin m) : ww i = w i.succ := rfl
  have hleft0 := WeightedCurveDegree.weightedPole_nonneg w zz
  have hright0 := WeightedCurveDegree.weightedPole_nonneg ww z
  apply le_antisymm
  · apply weightedPole_le w zz _ hright0
    intro i
    cases i using Fin.cases with
    | zero => simpa only [hz0, neg_zero, zero_div] using hright0
    | succ i =>
      rw [hzs]
      have hh := WeightedCurveDegree.div_le_weightedPole ww z i
      rw [hws] at hh
      exact hh
  · apply weightedPole_le ww z _ hleft0
    intro i
    have hh := WeightedCurveDegree.div_le_weightedPole w zz i.succ
    rw [hzs] at hh
    rw [hws]
    exact hh

theorem coordinatePole_const {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (p : CurveValuationCenter.NormalizedPlace ℂ E) (a : ℂ)
    (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    WeightedPolynomialPole.coordinatePole p.valuation (Fin.cases (algebraMap ℂ E a) x) w =
      WeightedPolynomialPole.coordinatePole p.valuation x (fun i => w i.succ) := by
  have h1 : WeightedPolynomialPole.coordinateOrder p.valuation (algebraMap ℂ E a) = 0 :=
    CurveContactSum.coordinateOrder_constant_eq_zero p a
  have he : (fun i : Fin (m+1) =>
      (WeightedPolynomialPole.coordinateOrder p.valuation
        ((Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) i) : ℚ)) =
      Fin.cases 0 (fun i => (WeightedPolynomialPole.coordinateOrder p.valuation (x i) : ℚ)) := by
    funext i
    cases i using Fin.cases <;> simp [h1]
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact weightedPole_zero_cons w _

theorem weightedDegree_const {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite
      (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ) := by
    ext p
    exact coordinatePole_const p a w x
  unfold CurveContactSum.weightedDegree
  rw [he]

end LogExponent.FibreContact
end

end OAI
