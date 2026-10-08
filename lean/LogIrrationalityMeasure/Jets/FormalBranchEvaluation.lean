import LogIrrationalityMeasure.Analysis.FormalLogTruncation
import LogIrrationalityMeasure.Jets.FormalBranchOrderRational

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.FormalBranchEvaluation
open MvPowerSeries
open FormalLogJet FormalLogTruncation

/-- The branch coordinate `t = y / c 0 - 1` along a branch `Y = y`. -/
def centeredY {m : ℕ} (c : Fin (m+1) → ℂ) (y : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C (c 0)⁻¹ * y - 1

theorem constantCoeff_centeredY {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (y : PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = c 0) :
    PowerSeries.constantCoeff (centeredY c y) = 0 := by
  simp [centeredY, hy, inv_mul_cancel₀ hc]

theorem centeredY_eq_zero_iff {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (y : PowerSeries ℂ) : centeredY c y = 0 ↔ y = PowerSeries.C (c 0) := by
  constructor
  · intro h
    have h1 : PowerSeries.C (c 0)⁻¹ * y = 1 := sub_eq_zero.mp h
    calc
      y = PowerSeries.C (c 0) * (PowerSeries.C (c 0)⁻¹ * y) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
      _ = PowerSeries.C (c 0) := by rw [h1, mul_one]
  · intro h
    simp [centeredY, h, ← map_mul, inv_mul_cancel₀ hc]

/-- The branch coordinates `(t, x_i - c i.succ - log(1 + t))` of a branch `(y, x)` at the
centre `c`. -/
def branchCoordinates {m : ℕ} (c : Fin (m+1) → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (centeredY c y) (fun i => x i - PowerSeries.C (c i.succ) -
    PowerSeries.subst (centeredY c y) (PowerSeries.log ℂ))

theorem branchCoordinates_hasSubst {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = c 0)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i.succ) :
    HasSubst (branchCoordinates c y x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  have ht : MvPowerSeries.constantCoeff (centeredY c y) = 0 :=
    constantCoeff_centeredY c hc y hy
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change MvPowerSeries.constantCoeff
      (x i - PowerSeries.C (c i.succ) - PowerSeries.subst (centeredY c y) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ (PowerSeries.constantCoeff_log),
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (x i) - PowerSeries.constantCoeff (PowerSeries.C (c i.succ)) = 0
    rw [hx i, PowerSeries.constantCoeff_C, sub_self]

theorem subst_liftSeries {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (ha : HasSubst a)
    (f : PowerSeries ℂ) :
    subst a (liftSeries m f) = PowerSeries.subst (a 0) f := by
  rw [liftSeries_eq_toMvPowerSeries, PowerSeries.subst_toMvPowerSeries ha]

theorem formalJet_subst_branch {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = c 0)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i.succ)
    (p : LogExponentApprox.FramePolynomial m) :
    subst (branchCoordinates c y x) (formalJet c p) =
      MvPolynomial.aeval (Fin.cases y x) p := by
  let ha := branchCoordinates_hasSubst c hc y x hy hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval (Fin.cases y x) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, formalJet_Y, map_add, map_one, map_mul, substAlgHom_X,
        MvPolynomial.aeval_X, Fin.cases_zero]
      rw [substAlgHom_apply, subst_C]
      change PowerSeries.C (c 0) * (1 + centeredY c y) = y
      simp only [centeredY, add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
        map_one, one_mul]
    | succ i =>
      simp only [AlgHom.comp_apply, formalJet_X, map_add,
        MvPolynomial.aeval_X, Fin.cases_succ]
      rw [substAlgHom_X]
      have hl : substAlgHom ha (formalLog m) =
          PowerSeries.subst (centeredY c y) (PowerSeries.log ℂ) := by
        rw [substAlgHom_apply, formalLog, subst_liftSeries _ ha]
        rfl
      rw [hl, substAlgHom_apply, subst_C]
      change PowerSeries.C (c i.succ) +
        (x i - PowerSeries.C (c i.succ) - PowerSeries.subst (centeredY c y) (PowerSeries.log ℂ)) +
        PowerSeries.subst (centeredY c y) (PowerSeries.log ℂ) = x i
      ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem polynomialFrameWord_branch_order {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = c 0)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i.succ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : LogExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1))) :
    (⌈μ * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (LogExponentApprox.polynomialFrameWord m word p)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv μ (H - (word.map v).sum) hμ
    (formalJet c (LogExponentApprox.polynomialFrameWord m word p)) (branchCoordinates c y x)
    (branchCoordinates_hasSubst c hc y x hy hx)
    (formalJet_polynomialFrameWord_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c hc y x hy hx] at h

theorem polynomialFrameWord_branch_order_toNat {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = c 0)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i.succ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : LogExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x)
      (LogExponentApprox.polynomialFrameWord m word p) ≠ 0) :
    μ * (H - (word.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (LogExponentApprox.polynomialFrameWord m word p))).toNat : ℚ) := by
  have h := polynomialFrameWord_branch_order c hc y x hy hx v hv μ H hμ p hp hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

end LogExponent.FormalBranchEvaluation

end

end LogIrrationalityMeasure
