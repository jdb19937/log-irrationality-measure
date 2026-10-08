import LogIrrationalityMeasure.Jets.CompactLogJetIdeal

namespace LogIrrationalityMeasure

noncomputable section
open scoped BigOperators
namespace LogExponent.JetProductLocalization
open CompactJetPolynomial LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def residueAlgHom : A →ₐ[ℂ] ℂ where
  __ := CurveLocalOrder.residueAugmentation ℂ A
  commutes' := CurveLocalOrder.residueAugmentation_algebraMap ℂ A

theorem residue_ne_zero_iff_isUnit (a : A) :
    CurveLocalOrder.residueAugmentation ℂ A a ≠ 0 ↔ IsUnit a := by
  change (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm
    ((IsLocalRing.residue A) a) ≠ 0 ↔ IsUnit a
  rw [map_ne_zero_iff _ (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm.injective,
    IsLocalRing.residue_ne_zero_iff_isUnit]

theorem residue_polynomial_aeval (a : A) (P : Polynomial ℂ) :
    CurveLocalOrder.residueAugmentation ℂ A (Polynomial.aeval a P) =
      P.eval (CurveLocalOrder.residueAugmentation ℂ A a) := by
  simpa [Polynomial.coe_aeval_eq_eval, residueAlgHom] using
    (Polynomial.aeval_algHom_apply (residueAlgHom (A := A)) a P).symm

theorem residue_centeredY {m : ℕ} (c : Fin (m+1) → ℂ) (y : A) :
    CurveLocalOrder.residueAugmentation ℂ A (centeredY c y) =
      (c 0)⁻¹ * CurveLocalOrder.residueAugmentation ℂ A y - 1 := by
  simp [centeredY, CurveLocalOrder.residueAugmentation_algebraMap]

theorem residue_centeredY_eq_zero {m : ℕ} (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (y : A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0) :
    CurveLocalOrder.residueAugmentation ℂ A (centeredY c y) = 0 := by
  rw [residue_centeredY, hy, inv_mul_cancel₀ hc, sub_self]

theorem residue_truncatedCoordinates_succ {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0) (i : Fin m) :
    CurveLocalOrder.residueAugmentation ℂ A (truncatedCoordinates c y x T i.succ) =
      CurveLocalOrder.residueAugmentation ℂ A (x i) - c i.succ := by
  have hlog : CurveLocalOrder.residueAugmentation ℂ A
      (Polynomial.aeval (centeredY c y) (PowerSeries.trunc (T i) (PowerSeries.log ℂ))) = 0 := by
    rw [residue_polynomial_aeval, residue_centeredY_eq_zero c hc y hy]
    exact logPolynomials_eval_zero T i
  simp only [truncatedCoordinates, Fin.cases_succ, map_sub,
    CurveLocalOrder.residueAugmentation_algebraMap, hlog, sub_zero]

theorem logarithmicIdeal_eq_top_of_residue_ne {m : ℕ}
    (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (y : A) (x : Fin m → A)
    (hne : ¬ (CurveLocalOrder.residueAugmentation ℂ A y = c 0 ∧
      ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ)) :
    logarithmicIdeal c y x T e = ⊤ := by
  classical
  have hunit : ∃ i : Fin (m+1), IsUnit (truncatedCoordinates c y x T i) := by
    by_cases hy : CurveLocalOrder.residueAugmentation ℂ A y = c 0
    · have hx : ¬ ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i.succ :=
        fun hx => hne ⟨hy, hx⟩
      obtain ⟨i, hi⟩ := not_forall.mp hx
      refine ⟨i.succ, (residue_ne_zero_iff_isUnit _).mp ?_⟩
      rw [residue_truncatedCoordinates_succ c hc T y x hy i]
      exact sub_ne_zero.mpr hi
    · refine ⟨0, (residue_ne_zero_iff_isUnit _).mp ?_⟩
      change CurveLocalOrder.residueAugmentation ℂ A (centeredY c y) ≠ 0
      rw [residue_centeredY]
      intro h
      apply hy
      have h1 : (c 0)⁻¹ * CurveLocalOrder.residueAugmentation ℂ A y = 1 := sub_eq_zero.mp h
      calc
        CurveLocalOrder.residueAugmentation ℂ A y =
            c 0 * ((c 0)⁻¹ * CurveLocalOrder.residueAugmentation ℂ A y) := by
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        _ = c 0 := by rw [h1, mul_one]
  obtain ⟨i, hi⟩ := hunit
  apply Ideal.eq_top_of_isUnit_mem _
    (show truncatedCoordinates c y x T i ^ e i ∈ logarithmicIdeal c y x T e from
      Ideal.subset_span (Set.mem_range_self i))
  exact hi.pow (e i)

theorem map_powerIdeal_eq_top_of_ne {J : Type*} {m : ℕ}
    (c : J → Fin (m+1) → ℂ) (hc : Function.Injective c) (hc0 : ∀ j, c j 0 ≠ 0)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A)
    (j k : J) (hkj : k ≠ j)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c j 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c j i.succ) :
    (powerIdeal (c k) (logPolynomials T) e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom = ⊤ := by
  rw [map_powerIdeal_aeval]
  apply logarithmicIdeal_eq_top_of_residue_ne (c k) (hc0 k)
  rintro ⟨hk0, hk⟩
  apply hkj
  apply hc
  funext i
  cases i using Fin.cases with
  | zero => exact hk0.symm.trans hy
  | succ i => exact (hk i).symm.trans (hx i)

omit [IsLocalRing A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)] in
theorem map_polynomialIdeal {J : Type*} [Fintype J] {m : ℕ}
    (c : J → Fin (m+1) → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (y : A) (x : Fin m → A) :
    (CompactLogJetIdeal.polynomialIdeal c T e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom =
        ∏ j, logarithmicIdeal (c j) y x T e := by
  unfold CompactLogJetIdeal.polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact map_powerIdeal_aeval (c j) T e y x

theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J] {m : ℕ}
    (c : J → Fin (m+1) → ℂ) (hc : Function.Injective c) (hc0 : ∀ j, c j 0 ≠ 0)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A) (j : J)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = c j 0)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c j i.succ) :
    (CompactLogJetIdeal.polynomialIdeal c T e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom = logarithmicIdeal (c j) y x T e := by
  classical
  rw [map_polynomialIdeal]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    rw [Ideal.one_eq_top]
    rw [← map_powerIdeal_aeval]
    exact map_powerIdeal_eq_top_of_ne c hc hc0 T e y x j k hkj hy hx
  · simp

theorem map_polynomialIdeal_eq_top_outside {J : Type*} [Fintype J] {m : ℕ}
    (c : J → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (y : A) (x : Fin m → A)
    (hout : ¬ ∃ j, CurveLocalOrder.residueAugmentation ℂ A y = c j 0 ∧
      ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c j i.succ) :
    (CompactLogJetIdeal.polynomialIdeal c T e).map
      (MvPolynomial.aeval (Fin.cases y x)).toRingHom = ⊤ := by
  rw [map_polynomialIdeal]
  rw [← Ideal.one_eq_top]
  apply Finset.prod_eq_one
  intro j _
  rw [Ideal.one_eq_top]
  exact logarithmicIdeal_eq_top_of_residue_ne (c j) (hc0 j) T e y x (fun h => hout ⟨j, h⟩)

end LogExponent.JetProductLocalization

end

end LogIrrationalityMeasure
