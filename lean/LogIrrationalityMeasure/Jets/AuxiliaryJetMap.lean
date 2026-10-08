import LogIrrationalityMeasure.Polynomials.AuxiliaryPolynomial

namespace LogIrrationalityMeasure

open scoped BigOperators
open Filter Topology

namespace LogExponent

/-- The jet at the centre `(y^j, j r)` with the logarithms replaced by `G`, as a polynomial in
`u` with coefficients in `ℂ[t]`: `Y ↦ y^j (1 + t)`, `X_i ↦ j r_i + G_i(t) + u_i`. -/
noncomputable def literalJetSubstitution {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) :
    LogExponentApprox.FramePolynomial m →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C (Polynomial.C (y ^ j) * (1 + Polynomial.X)))
    (fun i => MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) + MvPolynomial.X i))

noncomputable def literalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m + 1) → ℝ) (H : ℝ) (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) :
    LogExponentApprox.FramePolynomial m →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ => (Polynomial.lcoeff ℂ (ρ.2.val 0)).comp
    (((MvPolynomial.lcoeff (Polynomial ℂ)
      (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).restrictScalars ℂ).comp
        (literalJetSubstitution y r G ρ.1.val).toLinearMap))

@[simp] theorem literalJetEvaluation_apply {m : ℕ} (K : ℕ)
    (V : Fin (m + 1) → ℝ) (H : ℝ) (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (p : LogExponentApprox.FramePolynomial m)
    (ρ : Fin K × ↥(strictWeightedSimplex V H)) :
    literalJetEvaluation K V H y r G p ρ =
      ((literalJetSubstitution y r G ρ.1.val p).coeff
        (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).coeff (ρ.2.val 0) := rfl

theorem literalJetSubstitution_monomial {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) (e : Fin (m + 1) → ℕ) (z : ℂ) :
    literalJetSubstitution y r G j
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z) =
      MvPolynomial.C (Polynomial.C z) *
        InterpolationMatrix.monomialImage y r G j (e 0) (fun i => e i.succ) := by
  classical
  rw [literalJetSubstitution, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp only [InterpolationMatrix.exponentVector_apply, Fin.cases_zero, Fin.cases_succ,
    InterpolationMatrix.monomialImage, ← map_pow, mul_pow]
  rfl

theorem literalJetSubstitution_polynomialOfCoefficients {m : ℕ}
    (S : Finset (Fin (m + 1) → ℕ)) (x : S → ℂ)
    (y : ℂ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (j : ℕ) :
    literalJetSubstitution y r G j (polynomialOfCoefficients S x) =
      InterpolationMatrix.sectionImage y r G (fun c : S => c.val 0)
        (fun c i => c.val i.succ) x j := by
  classical
  change literalJetSubstitution y r G j
    (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)) = _
  simp only [map_sum, literalJetSubstitution_monomial, InterpolationMatrix.sectionImage]

theorem eventually_exists_literalJet_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m + 1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : ℂ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : LogExponentApprox.FramePolynomial m, p ≠ 0 ∧
      LogExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ ρ : Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)),
        ((literalJetSubstitution y r G ρ.1.val p).coeff
          (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).coeff (ρ.2.val 0) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨p, hp, hw, he⟩ := hN (literalJetEvaluation K (fun i => (V i : ℝ)) (a * N) y r G)
  refine ⟨p, hp, hw, ?_⟩
  intro ρ
  have h := congrFun he ρ
  simpa only [literalJetEvaluation_apply, Pi.zero_apply] using h

end LogExponent

end LogIrrationalityMeasure
