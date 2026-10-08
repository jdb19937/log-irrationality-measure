import LogIrrationalityMeasure.Approximation.GenericNormalRigidity
import LogIrrationalityMeasure.Geometry.CurveContact
import LogIrrationalityMeasure.Jets.PrimeNormalCotangent

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.CurveComponentRigidity

open scoped BigOperators
open LogExponentApprox NormalBasisRigidity

theorem residueY_ne_zero {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q) :
    primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0 := by
  intro h
  exact hY (Ideal.algebraMap_residueField_eq_zero.mp h)

def NormalProductComparison {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (w cost : Fin (m + 1) → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin (m + 1)),
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ j)) A →
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) (residueY_ne_zero Q hY) j)) B →
    (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j

def PersistentNormalComparison {m : ℕ} (w cost : Fin (m + 1) → ℝ)
    (M delta : ℝ) (F : FramePolynomial m) (P : Ideal (FramePolynomial m))
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) : Prop :=
  ∀ r : ℕ, r < m + 2 → ∀ Q : Ideal (FramePolynomial m), ∀ hQ : Q.IsPrime,
    ∀ hQP : Q ≤ P,
    Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes →
    Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes →
    1 ≤ Q.height → Q.height ≤ m →
    (∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
      ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
        polynomialFrameWord m word p ∈ Q) →
    @NormalProductComparison m Q hQ (fun h => hY (hQP h)) w cost M

theorem coordinate_constant_of_persistent_comparison {m : ℕ}
    (w cost : Fin (m + 1) → ℝ) (M delta : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta → polynomialFrameWord m word F ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta F P hY)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : ℂ, MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ P := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    exists_persistent_frame_component cost hcost delta hdelta F hF P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  have hYQ : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q := fun h => hY (hQP h)
  have hFQ : F ∈ Q := hQr.le
    (polynomial_mem_frameDerivativeIdeal cost ((r : ℝ) * delta) F
      (mul_nonneg (Nat.cast_nonneg r) hdelta))
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hF (by simpa only [h, Ideal.mem_bot] using hFQ)
  have hcomp := hcomparison r hr Q inferInstance hQP hQr hQnext hQlo hQhi hpersist
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (FramePolynomial m) Q.ResidueField
  have hker (p : FramePolynomial m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨c, hc⟩ := constant_zeroth_coordinate_of_generic_normal_separation
    (primeResidueMap Q) Q hker hQ0 (residueY_ne_zero Q hYQ)
    (weighted_normalBasis_exclusion _ _ w cost M hcomp hseparated)
  exact ⟨c, hQP hc⟩

theorem coordinate_eq_center_of_persistent_comparison {m : ℕ}
    (w cost : Fin (m + 1) → ℝ) (M delta : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta → polynomialFrameWord m word F ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta F P hY)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    (a : Fin (m + 1) → ℂ)
    (hcenter : ∀ p ∈ P, MvPolynomial.eval a p = 0) :
    MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C (a 0) ∈ P :=
  constant_coordinate_eq_center P a hcenter
    (coordinate_constant_of_persistent_comparison w cost M delta hcost hdelta
      F hF P hP hheight hY hvanish hcomparison hseparated)

end LogExponent.CurveComponentRigidity
end

end LogIrrationalityMeasure
