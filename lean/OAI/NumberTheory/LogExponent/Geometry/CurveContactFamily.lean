import OAI.NumberTheory.LogExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.LogExponent.LocalAlgebra.FibreContact

namespace OAI

noncomputable section
namespace LogExponent.CurveContactFamily

open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

/-- The curve in the fibre `Y = a` with `X`-coordinates `x`. -/
def fibre (a : ℂ) (x : Fin m → E) : Fin (m+1) → E := Fin.cases (algebraMap ℂ E a) x

@[simp] theorem fibre_zero (a : ℂ) (x : Fin m → E) : fibre a x 0 = algebraMap ℂ E a := rfl
@[simp] theorem fibre_succ (a : ℂ) (x : Fin m → E) (i : Fin m) : fibre a x i.succ = x i := rfl

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z c hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z c hz ↔ ∃ j : Fin K, Centered z (c j) p := by
  exact mem_centerPlaces z c hz hfinite p

def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) : Fin K :=
  Classical.choose ((mem_places hfinite z c hz p).mp hp)

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    Centered z (c (center hfinite z c hz p hp)) p :=
  Classical.choose_spec ((mem_places hfinite z c hz p).mp hp)

theorem nonconstant (z : Fin (m+1) → E) (c : Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E (c i) :=
  Centered.exists_nonzero_difference z c hz

def contact
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ)
    (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  letI := hres p
  exact if hp : p ∈ places hfinite z c hz then
    PlaceCenteredBranch.logContact p z (c (center hfinite z c hz p hp))
      (centered hfinite z c hz p hp) (nonconstant z _ hz) v
  else 0

theorem contact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    0 < contact hres hfinite z c hz v p := by
  let := hres p
  simpa only [contact, dite_eq_left hp] using
    PlaceCenteredBranch.logContact_pos p z (c (center hfinite z c hz p hp)) (hc0 _)
      (centered hfinite z c hz p hp) (nonconstant z _ hz) v hv

theorem contact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite z c hz v p := by
  by_cases hp : p ∈ places hfinite z c hz
  · exact (contact_pos hres hfinite z c hc0 hz v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem logWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin (m+1) → ℂ) (hc0 : ∀ j, c j 0 ≠ 0)
    (hz : ∃ i, Transcendental ℂ (z i)) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : LogExponentApprox.FramePolynomial m)
    (hF : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (LogExponentApprox.polynomialFrameWord m word F) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z c hz) :
    contact hres hfinite z c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (LogExponentApprox.polynomialFrameWord m word F)) : ℚ) := by
  let := hres p
  have h := PlaceCenteredBranch.logWord_field_order_lower p z
    (c (center hfinite z c hz p hp)) (hc0 _) (centered hfinite z c hz p hp)
    (nonconstant z _ hz) v hv H F (hF _) word hne
  simpa only [contact, dite_eq_left hp] using h

/-- A place of the curve `Y = a` centred at `c j` forces `a = c j 0`. -/
theorem center_zero_eq
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (x : Fin m → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite (fibre a x) c hz) :
    c (center hfinite (fibre a x) c hz p hp) 0 = a :=
  ((centered hfinite (fibre a x) c hz p hp).constant_coordinate 0 a rfl).symm

theorem contact_fibre
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (ha : a ≠ 0) (x : Fin m → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite (fibre a x) c hz) :
    letI := hres p
    contact hres hfinite (fibre a x) c hz v p =
      PlaceCenteredBranch.ordinaryContact p x
        (fun i => c (center hfinite (fibre a x) c hz p hp) i.succ)
        (fun i => centered hfinite (fibre a x) c hz p hp i.succ)
        (PlaceCenteredBranch.fibre_nonconstant x _
          (by rw [center_zero_eq hfinite a x c hz p hp]; exact nonconstant _ _ hz))
        (fun i => v i.succ) := by
  let := hres p
  dsimp only [contact]
  rw [dite_eq_left hp]
  have hcj := center_zero_eq hfinite a x c hz p hp
  have hcongr (b : Fin (m+1) → ℂ) (hb : b 0 = a) (hb0 : b 0 ≠ 0)
      (hc : Centered (fibre a x) b p)
      (hnc : ∃ i, (fibre a x) i ≠ algebraMap ℂ E (b i)) :
      PlaceCenteredBranch.logContact p (fibre a x) b hc hnc v =
        PlaceCenteredBranch.ordinaryContact p x (fun i => b i.succ) (fun i => hc i.succ)
          (PlaceCenteredBranch.fibre_nonconstant x _ (by rw [hb]; exact hnc))
          (fun i => v i.succ) := by
    subst hb
    exact PlaceCenteredBranch.logContact_fibre p x b hb0 hc hnc v
  exact hcongr _ hcj (by rw [hcj]; exact ha) _ _

theorem ordinaryWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (ha : a ≠ 0) (x : Fin m → E) (c : Fin K → Fin (m+1) → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre a x) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : MvPolynomial (Fin m) ℂ)
    (hF : ∀ j, OrdinaryAuxiliaryJet.formalJet (fun i => c j i.succ) F ∈
      JetGeometry.rationalWeightedIdeal (fun i => v i.succ)
        (fun i => (hv i.succ).le) H)
    (word : List (Fin m))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word m word F) ≠ 0)
    (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite (fibre a x) c hz) :
    contact hres hfinite (fibre a x) c hz v p *
        (H - (word.map (fun i => v i.succ)).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval x (OrdinaryDerivatives.word m word F)) : ℚ) := by
  let := hres p
  rw [contact_fibre hres hfinite a ha x c hz v p hp]
  exact PlaceCenteredBranch.ordinaryWord_field_order_lower p x _
    (fun i => centered hfinite (fibre a x) c hz p hp i.succ)
    (PlaceCenteredBranch.fibre_nonconstant x _
      (by rw [center_zero_eq hfinite a x c hz p hp]; exact nonconstant _ _ hz))
    (fun i => v i.succ) (fun i => hv i.succ) H F (hF _) word hne

end LogExponent.CurveContactFamily
end

end OAI
