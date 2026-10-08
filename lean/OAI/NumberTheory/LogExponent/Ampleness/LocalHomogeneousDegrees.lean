import Mathlib.RingTheory.Localization.AtPrime.Basic
import OAI.NumberTheory.LogExponent.LocalAlgebra.RegularDegreePositivity

namespace OAI

namespace LogExponentJets.W22

variable {k σ : Type*} [Field k]

theorem homogeneous_degrees_pos_of_local_regular
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime]
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T)))) :
    ∀ i, 0 < degrees i := by
  intro i
  let μ := algebraMap (MvPolynomial σ k) (Localization.AtPrime T)
  let imap : Fin (gs.map μ).length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hn : μ gs[i] ≠ 0 := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      LogExponentSiegel.W20.regular_sequence_term_ne_zero (gs.map μ) hreg imap
  have hu : ¬ IsUnit (μ gs[i]) := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      LogExponentSiegel.W20.regular_sequence_term_not_isUnit (gs.map μ) hreg imap
  by_contra hpos
  have hd : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hh : gs[i].IsHomogeneous 0 := by simpa only [hd] using hhom i
  have hg : gs[i] = MvPolynomial.C ((gs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hh)
  have hc : (gs[i]).coeff 0 ≠ 0 := by
    intro hc
    apply hn
    rw [hg, hc, map_zero, map_zero]
  apply hu
  rw [hg]
  exact ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C).map μ

end LogExponentJets.W22

end OAI
