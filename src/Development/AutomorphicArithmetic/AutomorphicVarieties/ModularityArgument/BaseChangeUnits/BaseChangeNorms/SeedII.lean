module

public import Mathlib.Data.Nat.Notation
public import Formalism.ConjugateSelfDual.Statement
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

section

variable {l : ℕ} [Fact l.Prime]

private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]

end
