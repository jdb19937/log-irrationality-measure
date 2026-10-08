import LogIrrationalityMeasure.Approximation.Arithmetic
import LogIrrationalityMeasure.Approximation.InterpolationMatrix
import LogIrrationalityMeasure.Approximation.RowTranslation

namespace LogIrrationalityMeasure

namespace LogExponent

open scoped BigOperators

namespace InterpolationMatrix

theorem entry_eq_binomial_product {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) :
    entry y r G j s β h α =
      (y ^ j) ^ h * ((∏ i, ((α i).choose (β i) : ℂ)) *
        (((1 + Polynomial.X) ^ h * ∏ i,
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)).coeff s)) := by
  classical
  have hexp := RowTranslation.shiftCoefficient_eq
    (fun i => Polynomial.C ((j : ℂ) * r i) + G i)
    (exponentVector β) (exponentVector α)
  rw [RowTranslation.shiftCoefficient, RowTranslation.shift_monomial_one] at hexp
  simp only [exponentVector_apply] at hexp
  have hp : (monomialImage y r G j h α).coeff (exponentVector β) =
      Polynomial.C ((y ^ j) ^ h) * (1 + Polynomial.X) ^ h * ∏ i,
        ((α i).choose (β i) : Polynomial ℂ) *
          (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i) := by
    rw [monomialImage, MvPolynomial.coeff_C_mul]
    simpa only [add_comm] using
      congrArg (fun x => Polynomial.C ((y ^ j) ^ h) * (1 + Polynomial.X) ^ h * x) hexp
  rw [entry, hp, Finset.prod_mul_distrib]
  have hc : (∏ i, ((α i).choose (β i) : Polynomial ℂ)) =
      Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) := by simp
  rw [hc]
  rw [show Polynomial.C ((y ^ j) ^ h) * (1 + Polynomial.X) ^ h *
      (Polynomial.C (∏ i, ((α i).choose (β i) : ℂ)) *
        ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) =
      Polynomial.C ((y ^ j) ^ h * ∏ i, ((α i).choose (β i) : ℂ)) *
        ((1 + Polynomial.X) ^ h *
          ∏ i, (Polynomial.C ((j : ℂ) * r i) + G i) ^ (α i - β i)) by
    rw [map_mul]; ring]
  rw [Polynomial.coeff_C_mul, mul_assoc]

theorem entry_eq_zero_of_not_le {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (β : Fin m → ℕ)
    (h : ℕ) (α : Fin m → ℕ) (hβα : ¬ ∀ i, β i ≤ α i) :
    entry y r G j s β h α = 0 := by
  classical
  push Not at hβα
  obtain ⟨i, hi⟩ := hβα
  rw [entry_eq_binomial_product]
  have hprod : (∏ k, ((α k).choose (β k) : ℂ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  rw [hprod, zero_mul, mul_zero]

theorem scalar_product_mul_coeff {m : ℕ} (q : Fin m → ℂ)
    (d : Fin m → ℕ) (P : Polynomial ℂ) (F : Fin m → Polynomial ℂ) (s : ℕ) :
    (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i).coeff s =
      (P * ∏ i, (Polynomial.C (q i) * F i) ^ d i).coeff s := by
  have he : P * ∏ i, (Polynomial.C (q i) * F i) ^ d i =
      Polynomial.C (∏ i, q i ^ d i) * (P * ∏ i, F i ^ d i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    ring
  rw [he, Polynomial.coeff_C_mul]

/-- The centre factor `α^{jh}` becomes an integer after scaling by `b^{j hmax}`,
`α = a / b`, `h ≤ hmax`. -/
theorem den_pow_mul_rat_pow_mem (α : ℚ) (j h hmax : ℕ) (hh : h ≤ hmax) :
    (α.den : ℂ) ^ (j * hmax) * ((α : ℂ) ^ j) ^ h ∈ (Int.castRingHom ℂ).range := by
  obtain ⟨k, hk⟩ : ∃ k, j * hmax = j * h + k :=
    ⟨j * hmax - j * h, by have := Nat.mul_le_mul_left j hh; omega⟩
  have hden : (α.den : ℂ) ≠ 0 := by exact_mod_cast α.den_nz
  refine ⟨α.num ^ (j * h) * (α.den : ℤ) ^ k, ?_⟩
  rw [← pow_mul, hk, pow_add, Rat.cast_def, div_pow]
  simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  field_simp

theorem entry_truncatedLog_cleared_int {m : ℕ} (α : ℚ)
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h hmax : ℕ) (β a : Fin m → ℕ) (ha : ∀ i, a i ≤ e i) (hh : h ≤ hmax) :
    (α.den : ℂ) ^ (j * hmax) * (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ a i) / (∏ i, (q i : ℂ) ^ β i) *
      entry (α : ℂ) (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => truncatedLog (T i)) j s β h a ∈ (Int.castRingHom ℂ).range := by
  classical
  by_cases hβa : ∀ i, β i ≤ a i
  swap
  · rw [entry_eq_zero_of_not_le _ _ _ _ _ _ _ _ hβa, mul_zero]
    exact (Int.castRingHom ℂ).range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ a i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (a i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβa i)).symm
  let z : Fin m → ℤ := fun i => (j : ℤ) * p i
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
        truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    simp only [z, Int.cast_mul, Int.cast_natCast]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_int Finset.univ
    T q e (fun i => a i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (a i) (β i)).trans (ha i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial ℤ).map (Int.castRingHom ℂ)) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((a i).choose (β i) : ℂ)) ∈ (Int.castRingHom ℂ).range := by
    apply (Int.castRingHom ℂ).range.prod_mem
    intro i hi
    exact ⟨((a i).choose (β i) : ℤ), by simp⟩
  have hscalar := scalar_product_mul_coeff (fun i => (q i : ℂ)) (fun i => a i - β i)
    ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
      truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, entry_eq_binomial_product]
  have hy := den_pow_mul_rat_pow_mem α j h hmax hh
  have he := (Int.castRingHom ℂ).range.mul_mem hy
    ((Int.castRingHom ℂ).range.mul_mem hchoose hclear)
  rw [← hscalar] at he
  convert he using 1
  ring

end InterpolationMatrix

namespace MatrixArithmetic

noncomputable def logWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℝ :=
  (⌈Real.log (q i)⌉₊ : ℝ)

noncomputable def columnScale {m : ℕ} (q : Fin m → ℕ) (a : Fin m → ℕ) : ℝ :=
  ∏ i, (q i : ℝ) ^ a i

noncomputable def rowScale {m : ℕ} (q : Fin m → ℕ) (b : Fin m → ℕ) : ℝ :=
  (columnScale q b)⁻¹

/-- The largest exponent of `Y` among the columns: `⌊H / w0⌋`. -/
noncomputable def maxDegree (w0 H : ℝ) : ℕ := ⌊H / w0⌋₊

/-- The extra row scaling `b^{j hmax}` clearing the centre factor `α^{jh}`, `α = a / b`. -/
noncomputable def centerScale (b j hmax : ℕ) : ℝ := (b : ℝ) ^ (j * hmax)

noncomputable def denominator {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ ⌊H / logWeights q i⌋₊

noncomputable def rationalCenters {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => (p i : ℂ) / (q i : ℂ)

noncomputable def truncationOrders {m : ℕ} (q : Fin m → ℕ) (F v0 : ℝ) : Fin m → ℕ :=
  fun i => ⌈F * logWeights q i / v0⌉₊

theorem columnScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) : 0 < columnScale q a := by
  exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)

theorem rowScale_pos {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) : 0 < rowScale q b :=
  inv_pos.mpr (columnScale_pos hq b)

theorem centerScale_pos {b : ℕ} (hb : 0 < b) (j hmax : ℕ) : 0 < centerScale b j hmax :=
  pow_pos (by exact_mod_cast hb) _

theorem log_centerScale (b j hmax : ℕ) :
    Real.log (centerScale b j hmax) = ((j : ℝ) * hmax) * Real.log b := by
  rw [centerScale, Real.log_pow]
  push_cast
  ring

theorem denominator_pos {m : ℕ} (q : Fin m → ℕ) (T : Fin m → ℕ) (H : ℝ) :
    0 < denominator q T H := by
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))

theorem log_columnScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (a : Fin m → ℕ) :
    Real.log (columnScale q a) = ∑ i, (a i : ℝ) * Real.log (q i) := by
  rw [columnScale, Real.log_prod (by
    intro i hi
    exact pow_ne_zero _ (by exact_mod_cast (hq i).ne'))]
  simp only [Real.log_pow]

theorem log_rowScale {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 0 < q i)
    (b : Fin m → ℕ) :
    Real.log (rowScale q b) = -(∑ i, (b i : ℝ) * Real.log (q i)) := by
  rw [rowScale, Real.log_inv, log_columnScale hq]

theorem log_denominator_le {m : ℕ} {q : Fin m → ℕ} (F v0 H : ℝ)
    (hF : 0 ≤ F) (hv0 : 0 < v0) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    Real.log (denominator q (truncationOrders q F v0) H) ≤
      H * (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i) := by
  have h := Arithmetic.truncation_denominator_log_le Finset.univ
    (logWeights q) F v0 H hF hv0 hH (fun i _ => hw i)
  rw [div_le_iff₀ hH] at h
  simpa [denominator, truncationOrders, mul_comm H] using h

noncomputable def rowWeightedSum {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * logWeights q i

noncomputable def meanRowWeight {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  rowWeightedSum K v0 θ q H /
    ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H)

noncomputable def rowCost {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i)

/-- The total logarithmic cost of the centre scalings `b^{j hmax}` over all rows. -/
noncomputable def centerCost {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (q : Fin m → ℕ) (b : ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ((ρ.1.val : ℝ) * maxDegree w0 H) * Real.log b

noncomputable def columnCost {m : ℕ} {K : ℕ} {w0 v0 θ : ℝ}
    (q : Fin m → ℕ) {H : ℝ}
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i)

noncomputable def selectedMinor {m : ℕ} (α : ℚ) (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (logWeights q) H) ℂ :=
  (InterpolationMatrix.truncatedLogMatrix (α : ℂ) K w0 v0 θ (logWeights q) H
    (rationalCenters p q) (truncationOrders q F v0)).submatrix id selection

theorem actual_row_card_pos {m K : ℕ} {v0 θ H : ℝ} {q : Fin m → ℕ}
    (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ) (hH : 0 < H)
    (hw : ∀ i, 0 < logWeights q i) :
    0 < Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  apply (InterpolationMatrix.row_mem_iff hv0 hθ hw _).mpr
  simpa using hH

theorem ceil_log_weight_pos {q : ℕ} (hq : 2 ≤ q) :
    0 < (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  exact lt_of_lt_of_le (Real.log_pos hqR) (Nat.le_ceil _)

theorem column_coordinate_le_floor {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (c : LogExponent.InterpolationMatrix.Column w0 w H) (i : Fin m) :
    c.1 i.succ ≤ ⌊H / w i⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  have hs : w i * (c.1 i.succ : ℝ) ≤
      ∑ j, w j * (c.1 j.succ : ℝ) :=
    Finset.single_le_sum (fun j hj => mul_nonneg (hw j).le (Nat.cast_nonneg (c.1 j.succ)))
      (Finset.mem_univ i)
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  have hb := LogExponent.InterpolationMatrix.column_weight_le hw0 hw c
  nlinarith only [hs, h0, hb]

theorem column_degree_le_maxDegree {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (c : LogExponent.InterpolationMatrix.Column w0 w H) :
    c.1 0 ≤ maxDegree w0 H := by
  apply Nat.le_floor
  apply (le_div_iff₀ hw0).mpr
  have hs : 0 ≤ ∑ j, w j * (c.1 j.succ : ℝ) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hw j).le (Nat.cast_nonneg (c.1 j.succ)))
  have hb := LogExponent.InterpolationMatrix.column_weight_le hw0 hw c
  nlinarith only [hs, hb]

theorem column_log_cost_le_H {m : ℕ} {w0 H : ℝ} (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (c : LogExponent.InterpolationMatrix.Column w0
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ i, (c.1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤ H := by
  have hb := LogExponent.InterpolationMatrix.column_weight_le hw0
    (fun i => ceil_log_weight_pos (hq i)) c
  have hc := LogExponent.Arithmetic.column_log_cost_le Finset.univ
    (fun i => c.1 i.succ) q
  have h0 : 0 ≤ w0 * (c.1 0 : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i, (c.1 i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉₊ : ℝ) := hc
    _ = ∑ i, (⌈Real.log (q i : ℝ)⌉₊ : ℝ) * (c.1 i.succ : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ ≤ H := by linarith

theorem selected_column_log_cost_le {m K : ℕ} {w0 v0 θ H : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : LogExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H →
      LogExponent.InterpolationMatrix.Column w0
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :
    (∑ ρ, ∑ i, ((selection ρ).1 i.succ : ℝ) * Real.log (q i : ℝ)) ≤
      (Fintype.card (LogExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) : ℝ) * H := by
  calc
    _ ≤ ∑ ρ, H := Finset.sum_le_sum (fun ρ hρ => column_log_cost_le_H q hq hw0 (selection ρ))
    _ = _ := by simp

theorem row_weighted_cost_le {m K : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (ρ : LogExponent.InterpolationMatrix.Row K v0 θ w H) :
    (∑ i, (ρ.2.1 i.succ : ℝ) * w i) ≤ H * θ := by
  have hb := LogExponent.InterpolationMatrix.row_weight_lt hv0 hθ hw ρ
  have h0 : 0 ≤ v0 * (ρ.2.1 0 : ℝ) := mul_nonneg hv0.le (Nat.cast_nonneg _)
  have hh : (∑ i, w i * (ρ.2.1 i.succ : ℝ)) / θ ≤ H := by linarith
  have hm := (div_le_iff₀ hθ).mp hh
  simpa only [mul_comm] using hm

theorem all_row_log_cost_lower {m K : ℕ} {v0 θ H wmin : ℝ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hv0 : 0 < v0) (hθ : 0 < θ) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) :
    (∑ ρ : LogExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H,
        ∑ i, (ρ.2.1 i.succ : ℝ) * (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) -
      (Fintype.card (LogExponent.InterpolationMatrix.Row K v0 θ
        (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) : ℝ) * H * θ / wmin ≤
    ∑ ρ : LogExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H,
        ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i : ℝ) := by
  have hrow (ρ : LogExponent.InterpolationMatrix.Row K v0 θ
      (fun i => (⌈Real.log (q i : ℝ)⌉₊ : ℝ)) H) :=
    LogExponent.Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ)
      q wmin (H * θ) hmin (fun i hi => hwmin i)
      (row_weighted_cost_le hv0 hθ (fun i => ceil_log_weight_pos (hq i)) ρ)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ρ hρ => hrow ρ)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_div_assoc, mul_assoc] using hs

theorem selectedMinor_entries_int {m K : ℕ} {w0 v0 θ F H : ℝ} (α : ℚ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (ρ σ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :
    (denominator q (truncationOrders q F v0) H : ℂ) *
      ((rowScale q (fun i => ρ.2.1 i.succ) *
        centerScale α.den ρ.1.val (maxDegree w0 H) : ℝ) : ℂ) *
        ((columnScale q (fun i => (selection σ).1 i.succ) : ℂ) *
          selectedMinor α K w0 v0 θ F H p q selection ρ σ) ∈
        (Int.castRingHom ℂ).range := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have he := InterpolationMatrix.entry_truncatedLog_cleared_int α
    (truncationOrders q F v0) q (fun i => ⌊H / logWeights q i⌋₊) p
    (fun i => by have := hq i; omega) ρ.1.val (ρ.2.1 0) ((selection σ).1 0)
    (maxDegree w0 H)
    (fun i => ρ.2.1 i.succ) (fun i => (selection σ).1 i.succ)
    (column_coordinate_le_floor hw0 hw (selection σ))
    (column_degree_le_maxDegree hw0 hw (selection σ))
  simp only [denominator, rowScale, columnScale, centerScale, selectedMinor,
    InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix,
    Matrix.submatrix_apply, id_eq,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    Complex.ofReal_inv, Complex.ofReal_mul]
  have hcenters : rationalCenters p q =
      (fun i => (p i : ℂ) / (q i : ℂ)) := rfl
  rw [← hcenters] at he
  convert he using 1
  ring

theorem selectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ} (α : ℚ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor α K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + (rowCost K v0 θ q H - centerCost K w0 v0 θ q α.den H) ≤
      Real.log ‖(selectedMinor α K w0 v0 θ F H p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hc := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor α K w0 v0 θ F H p q selection)
    (fun ρ => rowScale q (fun i => ρ.2.1 i.succ) *
      centerScale α.den ρ.1.val (maxDegree w0 H))
    (fun σ => columnScale q (fun i => (selection σ).1 i.succ))
    (denominator q (truncationOrders q F v0) H)
    (denominator_pos _ _ _)
    (fun ρ => mul_pos (rowScale_pos hqpos _) (centerScale_pos α.pos _ _))
    (fun σ => columnScale_pos hqpos _) hdet
    (selectedMinor_entries_int α p q hq hw0 selection)
  simp only [Real.log_mul (rowScale_pos hqpos _).ne' (centerScale_pos α.pos _ _).ne',
    log_rowScale hqpos, log_columnScale hqpos, log_centerScale,
    Finset.sum_add_distrib, Finset.sum_neg_distrib] at hc
  dsimp [columnCost, rowCost, centerCost]
  linarith

theorem centerCost_le {m K : ℕ} {w0 v0 θ H : ℝ} (q : Fin m → ℕ) (b : ℕ)
    (hb : 1 ≤ b) (hw0 : 0 < w0) (hH : 0 ≤ H) :
    centerCost K w0 v0 θ q b H ≤
      (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
        (((K : ℝ) - 1) * Real.log b / w0) := by
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  have hmax : (maxDegree w0 H : ℝ) ≤ H / w0 := Nat.floor_le (div_nonneg hH hw0.le)
  have hterm : ∀ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
      ((ρ.1.val : ℝ) * maxDegree w0 H) * Real.log b ≤
        H * (((K : ℝ) - 1) * Real.log b / w0) := by
    intro ρ
    have hj : (ρ.1.val : ℝ) ≤ (K : ℝ) - 1 := by
      have := ρ.1.isLt
      have h' : (ρ.1.val : ℝ) + 1 ≤ K := by exact_mod_cast this
      linarith
    have hj0 : (0 : ℝ) ≤ ρ.1.val := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ maxDegree w0 H := Nat.cast_nonneg _
    have h1 : (ρ.1.val : ℝ) * maxDegree w0 H ≤ ((K : ℝ) - 1) * (H / w0) :=
      mul_le_mul hj hmax hm0 (by linarith)
    calc
      ((ρ.1.val : ℝ) * maxDegree w0 H) * Real.log b ≤
          (((K : ℝ) - 1) * (H / w0)) * Real.log b :=
        mul_le_mul_of_nonneg_right h1 hlog
      _ = H * (((K : ℝ) - 1) * Real.log b / w0) := by ring
  calc
    centerCost K w0 v0 θ q b H ≤
        ∑ _ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
          H * (((K : ℝ) - 1) * Real.log b / w0) :=
      Finset.sum_le_sum (fun ρ _ => hterm ρ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem selectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 θ F H wmin : ℝ} (α : ℚ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor α K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / wmin +
        ((K : ℝ) - 1) * Real.log α.den / w0) ≤
      Real.log ‖(selectedMinor α K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply Arithmetic.normalized_arithmetic_bound _ _ _ _ _ _ _ _ _ _ hM hH
  · exact selectedMinor_clearing_bound α p q hq hw0 selection hdet
  · exact log_denominator_le F v0 H hF hv0 hH hw
  · exact selected_column_log_cost_le q hq hw0 selection
  · have hrow (ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H) :=
      Arithmetic.row_log_cost_lower Finset.univ (fun i => ρ.2.1 i.succ) q
        wmin (H * θ) hmin (fun i _ => hwmin i)
        (row_weighted_cost_le hv0 hθ hw ρ)
    have hr := Finset.sum_le_sum (s := Finset.univ) (fun ρ _ => hrow ρ)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hr
    have hb :
        (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
          meanRowWeight K v0 θ q H = rowWeightedSum K v0 θ q H := by
      unfold meanRowWeight
      field_simp [(mul_pos hM hH).ne']
    have hcenter := centerCost_le (K := K) (v0 := v0) (θ := θ) q α.den α.pos hw0 hH.le
    rw [hb]
    have hr' : rowWeightedSum K v0 θ q H -
        (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H *
          (θ / wmin) ≤ rowCost K v0 θ q H := by
      simpa only [rowWeightedSum, rowCost, logWeights, mul_div_assoc, mul_assoc] using hr
    linarith

theorem meanRowWeight_nonneg {m : ℕ} (K : ℕ) (v0 θ : ℝ) (q : Fin m → ℕ)
    {H : ℝ} (hH : 0 ≤ H) : 0 ≤ meanRowWeight K v0 θ q H := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro ρ hρ
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact mul_nonneg (Nat.cast_nonneg _) hH

theorem meanRowWeight_le_theta {m K : ℕ} {v0 θ H : ℝ} (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) (hK : 0 < K) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hH : 0 < H) : meanRowWeight K v0 θ q H ≤ θ := by
  have hw : ∀ i, 0 < logWeights q i := fun i => ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) := by
    exact_mod_cast actual_row_card_pos hK hv0 hθ hH hw
  apply (div_le_iff₀ (mul_pos hM hH)).mpr
  calc
    rowWeightedSum K v0 θ q H ≤
        ∑ _ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H, H * θ :=
      Finset.sum_le_sum (fun ρ hρ => row_weighted_cost_le hv0 hθ hw ρ)
    _ = θ * ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

noncomputable def minimumLogWeight {m : ℕ} [NeZero m] (q : Fin m → ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (logWeights q)

theorem minimumLogWeight_pos {m : ℕ} [NeZero m] (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) : 0 < minimumLogWeight q := by
  exact (Finset.lt_inf'_iff _).mpr (fun i hi => ceil_log_weight_pos (hq i))

theorem minimumLogWeight_le {m : ℕ} [NeZero m] (q : Fin m → ℕ) (i : Fin m) :
    minimumLogWeight q ≤ logWeights q i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem selectedMinor_arithmetic_lower_bound_minimum {m K : ℕ} [NeZero m]
    {w0 v0 θ F H : ℝ} (α : ℚ) (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor α K w0 v0 θ F H p q selection).det ≠ 0) :
    -(1 - meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights q i + θ / minimumLogWeight q +
        ((K : ℝ) - 1) * Real.log α.den / w0) ≤
      Real.log ‖(selectedMinor α K w0 v0 θ F H p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H) :=
  selectedMinor_arithmetic_lower_bound α p q hq hK hw0 hv0 hθ hF hH
    (minimumLogWeight_pos q hq) (minimumLogWeight_le q) selection hdet

end MatrixArithmetic

end LogExponent

end LogIrrationalityMeasure
