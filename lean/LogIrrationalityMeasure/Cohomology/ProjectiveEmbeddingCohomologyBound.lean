import LogIrrationalityMeasure.Approximation.ClosedImmersionSerreTransfer
import LogIrrationalityMeasure.Cohomology.SerreVanishing
import LogIrrationalityMeasure.Geometry.LineBundleCoherent
import LogIrrationalityMeasure.Geometry.ProjectiveSpaceBasics

namespace LogIrrationalityMeasure

namespace LogExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open LogExponentSeshadri.Geometry LogExponentSeshadri.Projective
open LogExponent.ProjectiveO1

theorem projectiveSpace_cohomology_eq_zero (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : r+1 ≤ q) (z : cohomology M q) : z = 0 := by
  exact LogExponent.SerreVanishing.ext_eq_zero_of_affine_cover (r+1) (by omega)
    (coordinateOpen (R := ℂ) (σ := Fin (r+1)))
    (fun j => standardChart_isAffineOpen j) standardChart_cover M q hq z

theorem cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : r+1 ≤ q)
    (z : cohomology M q) : z = 0 := by
  let N := (Scheme.Modules.pushforward i).obj M
  let : N.IsFinitePresentation := LogExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation i M
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  let e := LogExponent.ClosedImmersionSerreTransfer.closedCohomologyEquiv i M q
  apply e.injective
  exact (projectiveSpace_cohomology_eq_zero r N q hq (e z)).trans e.map_zero.symm

theorem lineBundle_cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (L : LineBundle X) (q : ℕ) (hq : r+1 ≤ q) (z : cohomology L.sheaf q) : z = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    LogExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact cohomology_eq_zero_of_projective_embedding r i L.sheaf q hq z

end
end LogExponent.NumericalAmpleness

end LogIrrationalityMeasure
