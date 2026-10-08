import OAI.NumberTheory.LogExponent.Ampleness.ReesExceptional

namespace OAI

namespace LogExponentSeshadri.ReesGrading
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalLineBundle_sheaf_eq :
    (exceptionalLineBundle I).sheaf = IdealModule.closedModule (exceptionalIdeal I) := rfl

end
end LogExponentSeshadri.ReesGrading

end OAI
