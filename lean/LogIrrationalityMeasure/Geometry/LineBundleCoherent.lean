import LogIrrationalityMeasure.LocalAlgebra.FiniteGlobalPresentation

namespace LogIrrationalityMeasure

namespace LogExponent.GeometrySupport.LineBundleCoherent

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LogExponentSeshadri.Geometry

variable {X : Scheme}

theorem structureSheaf_isFinitePresentation : (structureSheaf X).IsFinitePresentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ structureSheaf X :=
    coproductUniqueIso (fun _ : PUnit => structureSheaf X)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e
    (LogExponent.FiniteGlobalPresentation.free_isFinitePresentation X PUnit)

theorem lineBundle_isFinitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation := by
  let : (structureSheaf X).IsFinitePresentation := structureSheaf_isFinitePresentation
  apply LogExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso
    (structureSheaf X) L.sheaf
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm⟩⟩

theorem modulePow_isFinitePresentation (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsFinitePresentation :=
  lineBundle_isFinitePresentation (L.pow n)

theorem modulePow_isQuasicoherent (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsQuasicoherent := by
  have := modulePow_isFinitePresentation L n
  exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (modulePow X L.sheaf n)).choose.isQuasicoherent

end
end LogExponent.GeometrySupport.LineBundleCoherent

end LogIrrationalityMeasure
