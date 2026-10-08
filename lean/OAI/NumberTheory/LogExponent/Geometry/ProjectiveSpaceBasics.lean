import OAI.NumberTheory.LogExponent.Cohomology.CurveEuler
import OAI.NumberTheory.LogExponent.Geometry.ProjectiveO1ChartMap

namespace OAI

namespace LogExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LogExponentSeshadri.Geometry
variable (R σ : Type) [CommRing R]

instance projectiveSpace_noetherian [IsNoetherianRing R] [Finite σ] :
    IsNoetherian (projectiveSpace R σ) := by
  let : IsLocallyNoetherian (projectiveSpace R σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveProjection R σ)
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact {}

instance projectiveSpace_separated [Finite σ] : (projectiveSpace R σ).IsSeparated := by
  constructor
  have h : IsSeparated (polynomialProjectiveProjection R σ ≫
      terminal.from (Spec (CommRingCat.of R))) := inferInstance
  simpa only [terminal.comp_from] using h

instance projectiveSpace_diagonal_affine [Finite σ] :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveSpace R σ))) := by
  infer_instance

theorem scalars_eq_baseScalars :
    scalars (R := ℂ) (σ := σ) = baseScalars (polynomialProjectiveProjection ℂ σ) := rfl

end
end LogExponent.ProjectiveO1

end OAI
