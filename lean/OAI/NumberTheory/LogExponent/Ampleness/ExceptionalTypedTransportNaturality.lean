import OAI.NumberTheory.LogExponent.Ampleness.ExceptionalTypedRestriction
import OAI.NumberTheory.LogExponent.Ampleness.ExceptionalTypedTransport

namespace OAI

namespace LogExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open LogExponentSeshadri.Geometry LogExponentSeshadri.ModuleFlasque
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (hchart : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

theorem transportSections_restrict (L : LineBundle Y) (n : ℕ)
    {U V : Y.Opens} (hU : j.opensRange = U) (hV : j'.opensRange = V)
    (hVU : V ≤ U) (b : freeOpen Y.ringCatSheaf U ⟶ (L.pow n).sheaf) :
    transportSections j' L n hV (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b) =
      restrictSections j j' θ hchart L n (transportSections j L n hU b) := by
  subst U V
  simp [transportSections, restrictSections, freeOpenMap]
  change (𝟙 _ ≫ (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b)) =
    freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ (𝟙 _ ≫ b)
  exact (Category.id_comp _).trans
    (congrArg (fun c => freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ c)
      (Category.id_comp b).symm)

end
end LogExponent.ExceptionalRepresentedTypes

end OAI
