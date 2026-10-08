import LogIrrationalityMeasure.Geometry.ProjectiveCharts
import LogIrrationalityMeasure.Geometry.ProjectiveDenseChart
import LogIrrationalityMeasure.Geometry.ProjectiveRatioCocycle

namespace LogIrrationalityMeasure

noncomputable section
namespace LogExponent.ProjectiveO1
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R σ : Type) [CommRing R]

instance projectiveSpace_reduced [IsDomain R] : IsReduced (projectiveSpace R σ) := by
  let U : (projectiveSpace R σ).OpenCover :=
    (projectiveSpace R σ).openCoverOfIsOpenCover (coordinateOpen (R := R))
      (by exact standardChart_cover)
  have h (i : σ) : IsReduced (coordinateOpen (R := R) i).toScheme :=
    isReduced_of_isOpenImmersion (projectiveChartIso (R := R) i).hom
  let : ∀ i, IsReduced (U.X i) := h
  exact IsReduced.of_openCover _ U

instance projectiveSpace_irreducible [IsDomain R] [Nonempty σ] :
    IrreducibleSpace (projectiveSpace R σ) := by
  let i : σ := Classical.choice inferInstance
  let p : projectiveSpace R σ := projectiveGenericPoint (PolyGrade R σ)
    (poly_X_mem i) (by decide) (MvPolynomial.X_ne_zero i)
  have hp : closure ({p} : Set (projectiveSpace R σ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure (PolyGrade R σ) p x).mp
      (show (⊥ : HomogeneousIdeal (PolyGrade R σ)) ≤ x.asHomogeneousIdeal from bot_le)
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (projectiveSpace R σ))
  rw [← hp]
  exact (isIrreducible_singleton (x := p)).closure

instance projectiveSpace_integral [IsDomain R] [Nonempty σ] :
    IsIntegral (projectiveSpace R σ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end LogExponent.ProjectiveO1

end

end LogIrrationalityMeasure
