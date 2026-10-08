import Mathlib.RingTheory.Coprime.Lemmas
import LogIrrationalityMeasure.Jets.CompactJetPolynomial

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.JetPowerIdealCoprime
open MvPolynomial CompactJetPolynomial

variable {k : Type*} [Field k] {m : ℕ}

theorem pointIdeal_injective {σ : Type*} :
    Function.Injective (WeightedBezout.pointIdeal (k := k) (σ := σ)) := by
  intro a b hab
  funext i
  have hx : X i - C (a i) ∈ WeightedBezout.pointIdeal b := by
    rw [← hab]
    simp
  have hzero := (WeightedBezout.mem_pointIdeal b _).mp hx
  have hz : b i - a i = 0 := by simpa using hzero
  exact (sub_eq_zero.mp hz).symm

theorem powerIdeal_pairwise_isCoprime {J : Type*}
    (c : J → Fin (m+1) → k) (hc : Function.Injective c) (hc0 : ∀ j, c j 0 ≠ 0)
    (G : Fin m → Polynomial k) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun i j => IsCoprime (powerIdeal (c i) G e) (powerIdeal (c j) G e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (c i))
      (WeightedBezout.pointIdeal (c j)) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hij (hc (pointIdeal_injective heq))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdeal (c i) (hc0 i) G hG e he,
    radical_powerIdeal (c j) (hc0 j) G hG e he, hp.sup_eq, Ideal.radical_top]

theorem powerIdeal_pow_pairwise_isCoprime {J : Type*}
    (c : J → Fin (m+1) → k) (hc : Function.Injective c) (hc0 : ∀ j, c j 0 ≠ 0)
    (G : Fin m → Polynomial k) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (n : ℕ) :
    Pairwise (fun i j => IsCoprime (powerIdeal (c i) G e ^ n) (powerIdeal (c j) G e ^ n)) := by
  intro i j hij
  exact (powerIdeal_pairwise_isCoprime c hc hc0 G hG e he hij).pow

end LogExponent.JetPowerIdealCoprime

end

end LogIrrationalityMeasure
