import Mathlib

namespace LogIrrationalityMeasure

namespace LogExponent

open Filter

theorem exists_large_log_approximation
    (x : ℝ) (hx : x ≠ 0) (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  have hsmall : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (-nu) < |x| :=
    ((tendsto_rpow_neg_atTop hnu).comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (abs_pos.mpr hx))
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hsmall
  obtain ⟨p, q, hq, happrox⟩ := hbad (max (max 2 N) N')
  have hq2 : 2 ≤ q := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hq
  have hNq : N ≤ q := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hq
  have hN'q : N' ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  have hp : p ≠ 0 := by
    intro hp0
    have hx' : |x| ≤ (q : ℝ) ^ (-nu) := by
      simpa [hp0] using happrox
    exact absurd (hN' q hN'q) (not_lt.mpr hx')
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

end LogExponent

end LogIrrationalityMeasure
