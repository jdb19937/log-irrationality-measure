import LogIrrationalityMeasure.Jets.FormalBranchEvaluation

namespace LogIrrationalityMeasure

noncomputable section

namespace LogExponent.FormalBranchContact

open FormalBranchEvaluation FormalLogTruncation

def composedLogTails {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (T : Fin m → ℕ) :
    Fin (m+1) → PowerSeries ℂ :=
  Fin.cases 0 (fun i => PowerSeries.subst (a 0) (logTail (T i)))

def truncatedBranchCoordinates {m : ℕ} (c : Fin (m+1) → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (centeredY c y) (fun i => x i - PowerSeries.C (c i.succ) -
    PowerSeries.subst (centeredY c y)
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ))

theorem branchCoordinates_constantCoeff {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = c 0)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i.succ) :
    ∀ i, PowerSeries.constantCoeff (branchCoordinates c y x i) = 0 := by
  intro i
  have hh := (branchCoordinates_hasSubst c hc y x hy hx).const_coeff i
  have hz := isNilpotent_iff_eq_zero.mp hh
  simpa only [PowerSeries.constantCoeff_eq] using hz

theorem truncatedBranchCoordinates_eq_add_tail {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → ℕ) (hy : PowerSeries.constantCoeff y = c 0) :
    truncatedBranchCoordinates c y x T =
      fun i => branchCoordinates c y x i + composedLogTails (branchCoordinates c y x) T i := by
  have ht : PowerSeries.constantCoeff (centeredY c y) = 0 := constantCoeff_centeredY c hc y hy
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedBranchCoordinates, branchCoordinates, composedLogTails]
  | succ i =>
    simp only [truncatedBranchCoordinates, branchCoordinates, composedLogTails,
      Fin.cases_succ, Fin.cases_zero, logTail, PowerSeries.subst_sub hs]
    ring

theorem branchCoordinates_not_all_zero {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hne : y ≠ PowerSeries.C (c 0) ∨ ∃ i, x i ≠ PowerSeries.C (c i.succ)) :
    ∃ i, branchCoordinates c y x i ≠ 0 := by
  by_cases hy : y = PowerSeries.C (c 0)
  · obtain ⟨i, hi⟩ := hne.resolve_left (not_not.mpr hy)
    refine ⟨i.succ, ?_⟩
    have h0 : centeredY c y = 0 := (centeredY_eq_zero_iff c hc y).mpr hy
    simpa [branchCoordinates, h0, PowerSeries.subst_zero_of_constantCoeff_zero
      PowerSeries.constantCoeff_log, sub_eq_zero] using hi
  · refine ⟨0, ?_⟩
    change centeredY c y ≠ 0
    exact fun h => hy ((centeredY_eq_zero_iff c hc y).mp h)

end LogExponent.FormalBranchContact

end

end LogIrrationalityMeasure
