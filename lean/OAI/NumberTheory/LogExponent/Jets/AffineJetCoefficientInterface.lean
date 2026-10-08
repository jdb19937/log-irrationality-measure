import OAI.NumberTheory.LogExponent.Jets.AffineJetPolynomial

namespace OAI

noncomputable section
namespace LogExponent.AffineJetCoefficientInterface
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry
open LogExponent.ExceptionalAffineChart
variable {X : Scheme} {R : Type} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (A : LineBundle X)

def Frame : Type := A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme

def Sections (n : ℕ) : Type := GlobalSections X (modulePow X A.sheaf n)

def coefficient (n : ℕ) (e : Frame j A) : Sections A n → R :=
  AffineJetPolynomial.polynomialCoefficient j A n e

theorem coefficient_eq (n : ℕ) (e : Frame j A) (s : Sections A n) :
    coefficient j A n e s = AffineJetPolynomial.polynomialCoefficient j A n e s := rfl

end LogExponent.AffineJetCoefficientInterface
end

end OAI
