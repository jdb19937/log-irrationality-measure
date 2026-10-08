import LogIrrationalityMeasure.Jets.BranchContactIdeal
import LogIrrationalityMeasure.Jets.DVRBranchJet
import LogIrrationalityMeasure.Jets.FormalBranchContact

namespace LogIrrationalityMeasure

noncomputable section

namespace LogExponent.LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

/-- The local coordinate `y / c 0 - 1` of a point `y` of a `ℂ`-algebra. -/
def centeredY {m : ℕ} (c : Fin (m+1) → ℂ) (y : A) : A := algebraMap ℂ A (c 0)⁻¹ * y - 1

def truncatedCoordinates {m : ℕ} (c : Fin (m+1) → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) : Fin (m+1) → A :=
  Fin.cases (centeredY c y) (fun i => x i - algebraMap ℂ A (c i.succ) -
    Polynomial.aeval (centeredY c y) (PowerSeries.trunc (T i) (PowerSeries.log ℂ)))

def logarithmicIdeal {m : ℕ} (c : Fin (m+1) → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal A :=
  BranchContactIdeal.powerIdeal (truncatedCoordinates c y x T) e

theorem expansion_polynomial_aeval (z : A) (p : Polynomial ℂ) :
    DVRBranch.expansion ℂ A (Polynomial.aeval z p) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) p := by
  have hh : (DVRBranch.expansion ℂ A).comp (Polynomial.aeval z) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) := by
    apply Polynomial.algHom_ext
    simp
  exact AlgHom.congr_fun hh p

theorem expansion_centeredY {m : ℕ} (c : Fin (m+1) → ℂ) (y : A) :
    DVRBranch.expansion ℂ A (centeredY c y) =
      FormalBranchEvaluation.centeredY c (DVRBranch.expansion ℂ A y) := by
  simp [centeredY, FormalBranchEvaluation.centeredY, AlgHom.commutes]

theorem expansion_truncatedCoordinates {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A) (x : Fin m → A) (T : Fin m → ℕ)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0) :
    (fun i => DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i)) =
      FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i)) T := by
  have ht : PowerSeries.constantCoeff
      (FormalBranchEvaluation.centeredY c (DVRBranch.expansion ℂ A y)) = 0 :=
    FormalBranchEvaluation.constantCoeff_centeredY c hc _ (by simp [hy])
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero =>
    simp [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates,
      expansion_centeredY]
  | succ i =>
    simp only [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates,
      Fin.cases_succ, map_sub, AlgHom.commutes, expansion_polynomial_aeval,
      expansion_centeredY]
    rw [PowerSeries.subst_coe hs]
    rfl

theorem truncatedCoordinates_nonzero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ)
    (hnc : y ≠ algebraMap ℂ A (c 0) ∨ ∃ i, x i ≠ algebraMap ℂ A (c i.succ))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedCoordinates c y x T i ≠ 0 := by
  have hn := FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c hc
    (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
    (DVRBranchJet.coordinates_nonzero c y x hnc) T hT
  rw [← expansion_truncatedCoordinates c hc y x T hy] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  change DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i) = 0
  rw [hz, map_zero]

theorem branchContact_congr {ι : Type*} [Fintype ι]
    (v : ι → ℚ) (a b : ι → PowerSeries ℂ)
    (ha : ∃ i, a i ≠ 0) (hb : ∃ i, b i ≠ 0) (hab : a = b) :
    BranchContact.contact v a ha = BranchContact.contact v b hb := by
  subst b
  rfl

theorem truncated_contact_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ)
    (hnc : y ≠ algebraMap ℂ A (c 0) ∨ ∃ i, x i ≠ algebraMap ℂ A (c i.succ))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContactIdeal.contact v (truncatedCoordinates c y x T)
      (truncatedCoordinates_nonzero v hv c hc y x hy hx hnc T hT) =
        DVRBranchJet.contact v c y x hnc := by
  unfold BranchContactIdeal.contact DVRBranchJet.contact
  trans BranchContact.contact v
    (FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i)) T)
    (FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c hc
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT)
  · apply branchContact_congr
    exact expansion_truncatedCoordinates c hc y x T hy
  · exact FormalBranchContact.contact_truncatedBranchCoordinates_eq v hv c hc
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT

theorem logarithmicIdeal_colength_eq_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ)
    (hnc : y ≠ algebraMap ℂ A (c 0) ∨ ∃ i, x i ≠ algebraMap ℂ A (c i.succ))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ logarithmicIdeal c y x T e)).toNat : ℚ) =
      R * DVRBranchJet.contact v c y x hnc := by
  change ((Module.length A (A ⧸ BranchContactIdeal.powerIdeal
    (truncatedCoordinates c y x T) e)).toNat : ℚ) = _
  rw [BranchContactIdeal.colength_eq_contact v hv _
    (truncatedCoordinates_nonzero v hv c hc y x hy hx hnc T hT) R e he,
    truncated_contact_eq v hv c hc y x hy hx hnc T hT]

theorem logarithmicIdeal_colength_ne_top {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ)
    (hnc : y ≠ algebraMap ℂ A (c 0) ∨ ∃ i, x i ≠ algebraMap ℂ A (c i.succ))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    Module.length A (A ⧸ logarithmicIdeal c y x T e) ≠ ⊤ := by
  obtain ⟨i, hi, heq, _⟩ := BranchContactIdeal.exists_generator_colength_eq_contact
    v hv (truncatedCoordinates c y x T)
    (truncatedCoordinates_nonzero v hv c hc y x hy hx hnc T hT) R e he
  change Module.length A (A ⧸ BranchContactIdeal.powerIdeal
    (truncatedCoordinates c y x T) e) ≠ ⊤
  rw [heq]
  exact CurveLocalOrder.principal_colength_ne_top (pow_ne_zero _ hi)

end LogExponent.LogarithmicContactIdeal

end

end LogIrrationalityMeasure
