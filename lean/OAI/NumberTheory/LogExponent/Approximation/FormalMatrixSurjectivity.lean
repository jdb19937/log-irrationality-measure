import OAI.NumberTheory.LogExponent.Approximation.FormalMatrixBridge
import OAI.NumberTheory.LogExponent.Jets.FormalJetIndices

namespace OAI

noncomputable section

namespace LogExponent.FormalMatrixBridge

open MvPowerSeries

theorem truncatedLogMatrix_surjective_of_rational_packets {m : ℕ} {α : Type*}
    (y : ℂ) (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (P : α → LogExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, LogExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (FormalLogTruncation.truncatedFormalJet (rowCenter y r j.val) T (P a)))) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix y K w0 v0 θ w (H : ℝ) r T).mulVecLin := by
  classical
  have hrow' : (fun i => (V i : ℝ)) = InterpolationMatrix.rowWeights v0 θ w := funext hrow
  have hW : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i := by
    intro i
    exact Fin.cases hw0 hw i
  intro yv
  let e := rationalJetIndexEquiv V hV H
  let z : Fin K → JetGeometry.RationalCoefficientPacket (R := ℂ) V H :=
    fun j d => yv (j, ⟨(e d).val, by
      simpa only [← hrow'] using (e d).property⟩)
  obtain ⟨a, ha⟩ := hpacket z
  let x : InterpolationMatrix.Column w0 w (H : ℝ) → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  rw [truncatedLogMatrix_mulVec_eq_coeff]
  change coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (FormalLogTruncation.truncatedFormalJet (rowCenter y r ρ.1.val) T
      (polynomialOfCoefficients
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) (H : ℝ))
        (fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)))) = yv ρ
  rw [polynomialOfCoefficients_of_weighted _ hW _ (P a) (hdegree a)]
  let b : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) :=
    ⟨ρ.2.val, by simpa only [hrow'] using ρ.2.property⟩
  have hh := congrFun (congrFun ha ρ.1) (e.symm b)
  change coeff (e.symm b).val
    (FormalLogTruncation.truncatedFormalJet (rowCenter y r ρ.1.val) T (P a)) =
      z ρ.1 (e.symm b) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, b, z, Equiv.apply_symm_apply] using hh

theorem truncatedLogMatrix_surjective_of_formalLog_packets {m : ℕ} {α : Type*}
    (y : ℂ) (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT : ∀ i, V i.succ ≤ (T i : ℚ) * V 0)
    (P : α → LogExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, LogExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin K =>
      JetGeometry.rationalCoefficientPacket V H
        (FormalLogJet.formalJet (rowCenter y r j.val) (P a)))) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix y K w0 v0 θ w (H : ℝ) r T).mulVecLin := by
  apply truncatedLogMatrix_surjective_of_rational_packets
    y K w0 v0 θ w H hw0 hw V hV hrow r T P hdegree
  exact (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    V (fun i => (hV i).le) H T hT (fun j : Fin K => rowCenter y r j.val) P).mp hpacket

end LogExponent.FormalMatrixBridge

end

end OAI
