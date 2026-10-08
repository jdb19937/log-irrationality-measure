import OAI.NumberTheory.LogExponent.Analysis.FormalLogTruncation
import OAI.NumberTheory.LogExponent.Jets.PolynomialJetPackets

namespace OAI

noncomputable section
namespace LogExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [Field R] {m : ℕ}

/-- The polynomial jet at the centre `c` (Y-centre `c 0`): `Y ↦ c 0 (1 + Y)`,
`X_i ↦ c i.succ + X_i + G_i(Y)`. -/
def triangularMap (c : Fin (m+1) → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (C (c 0) * (1 + X 0))
    (fun i => C (c i.succ) + X i.succ + Polynomial.aeval (X 0) (G i)))

/-- The local coordinate `t = Y / c 0 - 1` at the centre. -/
def centeredY (c : Fin (m+1) → R) : MvPolynomial (Fin (m+1)) R := C (c 0)⁻¹ * X 0 - 1

def inverseTriangularMap (c : Fin (m+1) → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (centeredY c)
    (fun i => X i.succ - C (c i.succ) - Polynomial.aeval (centeredY c) (G i)))

@[simp] theorem triangularMap_X_zero (c : Fin (m+1) → R) (G : Fin m → Polynomial R) :
    triangularMap c G (X 0) = C (c 0) * (1 + X 0) := by simp [triangularMap]

@[simp] theorem triangularMap_X_succ (c : Fin (m+1) → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    triangularMap c G (X i.succ) = C (c i.succ) + X i.succ + Polynomial.aeval (X 0) (G i) := by
  simp [triangularMap]

@[simp] theorem inverseTriangularMap_X_zero (c : Fin (m+1) → R) (G : Fin m → Polynomial R) :
    inverseTriangularMap c G (X 0) = centeredY c := by simp [inverseTriangularMap]

@[simp] theorem inverseTriangularMap_X_succ (c : Fin (m+1) → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    inverseTriangularMap c G (X i.succ) =
      X i.succ - C (c i.succ) - Polynomial.aeval (centeredY c) (G i) := by
  simp [inverseTriangularMap]

theorem triangularMap_centeredY (c : Fin (m+1) → R) (hc : c 0 ≠ 0)
    (G : Fin m → Polynomial R) : triangularMap c G (centeredY c) = X 0 := by
  have h : (C (c 0)⁻¹ : MvPolynomial (Fin (m+1)) R) * C (c 0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  simp only [centeredY, map_sub, map_mul, map_one, MvPolynomial.algHom_C, triangularMap_X_zero,
    MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, h, one_mul]
  ring

theorem inverseTriangularMap_X_zero_image (c : Fin (m+1) → R) (hc : c 0 ≠ 0)
    (G : Fin m → Polynomial R) : inverseTriangularMap c G (C (c 0) * (1 + X 0)) = X 0 := by
  have h : (C (c 0) : MvPolynomial (Fin (m+1)) R) * C (c 0)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  simp only [map_mul, map_add, map_one, MvPolynomial.algHom_C, inverseTriangularMap_X_zero,
    centeredY, MvPolynomial.algebraMap_eq]
  rw [show (1 : MvPolynomial (Fin (m+1)) R) + (C (c 0)⁻¹ * X 0 - 1) = C (c 0)⁻¹ * X 0 by ring,
    ← mul_assoc, h, one_mul]

theorem triangularMap_comp_inverse (c : Fin (m+1) → R) (hc : c 0 ≠ 0)
    (G : Fin m → Polynomial R) :
    (triangularMap c G).comp (inverseTriangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [triangularMap_centeredY c hc G]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      triangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, triangularMap_centeredY c hc G, AlgHom.id_apply]
    ring

theorem inverseTriangularMap_comp (c : Fin (m+1) → R) (hc : c 0 ≠ 0)
    (G : Fin m → Polynomial R) :
    (inverseTriangularMap c G).comp (triangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [inverseTriangularMap_X_zero_image c hc G]
  | succ i =>
    simp only [AlgHom.comp_apply, triangularMap_X_succ, map_add,
      inverseTriangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, inverseTriangularMap_X_zero, AlgHom.id_apply]
    ring

def triangularEquiv (c : Fin (m+1) → R) (hc : c 0 ≠ 0) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R ≃ₐ[R] MvPolynomial (Fin (m+1)) R :=
  AlgEquiv.ofAlgHom (triangularMap c G) (inverseTriangularMap c G)
    (triangularMap_comp_inverse c hc G) (inverseTriangularMap_comp c hc G)

theorem liftSeries_polynomial (p : Polynomial R) :
    FormalLogJet.liftSeries m (p : PowerSeries R) =
      Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1))) p := by
  have h : (FormalLogJet.liftSeries (R := R) m).comp Polynomial.coeToPowerSeries.ringHom =
      (Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1)))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPowerSeries.algebraMap_apply]
    · simp
  exact RingHom.congr_fun h p

theorem truncatedFormalJet_eq_polynomial (c : Fin (m+1) → ℂ) (T : Fin m → ℕ)
    (P : LogExponentApprox.FramePolynomial m) :
    FormalLogTruncation.truncatedFormalJet c T P =
      ((triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) :
        MvPowerSeries (Fin (m+1)) ℂ) := by
  have h : FormalLogTruncation.truncatedFormalJet c T =
      (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
        (triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp [FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp only [FormalLogTruncation.truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, AlgHom.comp_apply, triangularMap_X_succ, map_add]
      rw [liftSeries_polynomial, ← Polynomial.aeval_algHom_apply]
      simp [MvPowerSeries.algebraMap_apply]
  simpa using AlgHom.congr_fun h P

theorem truncatedFormalJet_inverse (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) :
    FormalLogTruncation.truncatedFormalJet c T
      (inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) =
      (P : MvPowerSeries (Fin (m+1)) ℂ) := by
  rw [truncatedFormalJet_eq_polynomial]
  have h := AlgHom.congr_fun
    (triangularMap_comp_inverse c hc (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) P
  simpa using congrArg (fun Q : MvPolynomial (Fin (m+1)) ℂ =>
    (Q : MvPowerSeries (Fin (m+1)) ℂ)) h

theorem quotient_surjective_of_packet {A : Type*} [CommRing A] [Algebra R A]
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : A →ₐ[R] MvPowerSeries (Fin (m+1)) R)
    (hf : Function.Surjective (fun p => JetGeometry.rationalCoefficientPacket v H (f p))) :
    Function.Surjective ((Ideal.Quotient.mkₐ R (JetGeometry.rationalWeightedIdeal v hv H)).comp f) := by
  intro q
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨p, hp⟩ := hf (JetGeometry.rationalCoefficientPacket v H F)
  refine ⟨p, ?_⟩
  change Ideal.Quotient.mk _ (f p) = Ideal.Quotient.mk _ F
  apply Ideal.Quotient.eq.mpr
  exact (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv H _ _).mp hp

def algebraicJetMap (c : Fin (m+1) → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    LogExponentApprox.FramePolynomial m →ₐ[ℂ]
      MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H :=
  (Ideal.Quotient.mkₐ ℂ (JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H)).comp
    (FormalLogTruncation.truncatedFormalJet c T)

def algebraicJetIdeal (c : Fin (m+1) → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (LogExponentApprox.FramePolynomial m) :=
  RingHom.ker (algebraicJetMap c T v hv H)

@[simp] theorem mem_algebraicJetIdeal (c : Fin (m+1) → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (P : LogExponentApprox.FramePolynomial m) :
    P ∈ algebraicJetIdeal c T v hv H ↔
      FormalLogTruncation.truncatedFormalJet c T P ∈ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H := by
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

theorem truncatedFormalJet_packet_surjective (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : LogExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet c T P)) := by
  intro packet
  obtain ⟨P, hP⟩ := PolynomialJetPackets.polynomial_packet_surjective v hv H packet
  refine ⟨inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P, ?_⟩
  simpa only [truncatedFormalJet_inverse c hc] using hP

theorem algebraicJetMap_surjective (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (algebraicJetMap c T v (fun i => (hv i).le) H) :=
  quotient_surjective_of_packet v (fun i => (hv i).le) H _
    (truncatedFormalJet_packet_surjective c hc T v hv H)

def algebraicJetQuotientEquiv (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    (LogExponentApprox.FramePolynomial m ⧸ algebraicJetIdeal c T v (fun i => (hv i).le) H) ≃ₐ[ℂ]
      (MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v (fun i => (hv i).le) H) :=
  Ideal.quotientKerAlgEquivOfSurjective (algebraicJetMap_surjective c hc T v hv H)

@[simp] theorem algebraicJetQuotientEquiv_mk (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (P : LogExponentApprox.FramePolynomial m) :
    algebraicJetQuotientEquiv c hc T v hv H (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (FormalLogTruncation.truncatedFormalJet c T P) :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ P

theorem independent_truncatedFormalJet_packets_surjective {J : Type*}
    (c : J → Fin (m+1) → ℂ) (hc : ∀ j, c j 0 ≠ 0) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : J → LogExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet (c j) T (P j))) := by
  intro packets
  choose P hP using fun j => truncatedFormalJet_packet_surjective (c j) (hc j) T v hv H (packets j)
  exact ⟨P, funext hP⟩

theorem formalJet_packet_surjective (c : Fin (m+1) → ℂ) (hc : c 0 ≠ 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : LogExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogJet.formalJet c P)) := by
  let T : Fin m → ℕ := fun i => Nat.ceil (v i.succ / v 0)
  have hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0 := by
    intro i
    exact (div_le_iff₀ (hv 0)).mp (Nat.le_ceil _)
  have ht : Function.Surjective (fun P : LogExponentApprox.FramePolynomial m =>
      fun _ : Unit => JetGeometry.rationalCoefficientPacket v H
        (FormalLogTruncation.truncatedFormalJet c T P)) := by
    intro packets
    obtain ⟨P, hP⟩ := truncatedFormalJet_packet_surjective c hc T v hv H (packets ())
    refine ⟨P, ?_⟩
    funext j
    cases j
    exact hP
  have hs := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    v (fun i => (hv i).le) H T hT (fun _ : Unit => c) (fun P => P)).mpr ht
  intro packet
  obtain ⟨P, hP⟩ := hs (fun _ => packet)
  exact ⟨P, congrFun hP ()⟩

end LogExponent.AlgebraicJetPackets

end

end OAI
